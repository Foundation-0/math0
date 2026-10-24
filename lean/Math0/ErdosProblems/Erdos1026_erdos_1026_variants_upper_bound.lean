/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1026»
import Math0.Audit

/-!
# Erdős Problem 1026: the constant `c` is at most `1` (Cambie's construction)

Erdős Problem 1026 (erdosproblems.com/1026, in van Doorn's formulation) asks for the largest `c`
such that every sequence of `n` distinct positive reals has a monotone subsequence whose sum is at
least `(c - o(1)) n^{-1/2} ∑ xᵢ`. We prove the upstream statement `1 ∈ upperBounds
admissibleConstants`, i.e. no constant `c > 1` is admissible. The proof uses Cambie's
construction: for `n = k ^ 2` split the indices into `k` consecutive blocks of length `k`, make
the values increase inside each block and decrease from block to block, all within `[1, 1 + 1/k]`.
An increasing subsequence meets only one block and a decreasing one meets each block at most once,
so every monotone subsequence has at most `k` terms and sum at most `k + 1`, while the total sum
is at least `k ^ 2`; this rules out every `c > 1` once `k` is large.
-/

namespace Math0.Erdos1026

/-- The block-reversed rank of `i`: block `i / k` contributes `-k * (i / k)`, position `i % k`
within the block contributes `i % k`. -/
noncomputable def rank (k i : ℕ) : ℝ := ((i % k : ℕ) : ℝ) - (k : ℝ) * ((i / k : ℕ) : ℝ)

/-- Within a block the rank increases; across blocks it decreases. -/
theorem rank_cases {k i j : ℕ} (hk : 0 < k) (hij : i < j) :
    (i / k = j / k ∧ rank k i < rank k j) ∨ (i / k < j / k ∧ rank k j < rank k i) := by
  have hdiv : i / k ≤ j / k := Nat.div_le_div_right hij.le
  have hi := Nat.div_add_mod i k
  have hj := Nat.div_add_mod j k
  have hik := Nat.mod_lt i hk
  have hjk := Nat.mod_lt j hk
  rcases hdiv.lt_or_eq with h | h
  · right
    refine ⟨h, ?_⟩
    have h1 : ((i / k : ℕ) : ℝ) + 1 ≤ ((j / k : ℕ) : ℝ) := by exact_mod_cast h
    have h2 : ((j % k : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
    have h3 : (0 : ℝ) ≤ ((i % k : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    unfold rank
    nlinarith
  · left
    refine ⟨h, ?_⟩
    have hlt : i % k < j % k := by
      rw [h] at hi
      omega
    unfold rank
    rw [h]
    have : ((i % k : ℕ) : ℝ) < ((j % k : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith

/-- Bounds on the rank for `i < k ^ 2`. -/
theorem rank_bounds {k i : ℕ} (hk : 0 < k) (hi : i < k ^ 2) :
    0 ≤ rank k i + (k : ℝ) ^ 2 ∧ rank k i + (k : ℝ) ^ 2 ≤ 2 * (k : ℝ) ^ 2 := by
  have h1 := Nat.mod_lt i hk
  have h2 : k * (i / k) ≤ i := Nat.mul_div_le i k
  have h3 : ((i % k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1.le
  have h4 : (k : ℝ) * ((i / k : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : k * (i / k) ≤ k ^ 2 := by omega
    exact_mod_cast this
  have h5 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h6 : (0 : ℝ) ≤ ((i % k : ℕ) : ℝ) := Nat.cast_nonneg _
  have h7 : (0 : ℝ) ≤ (k : ℝ) * ((i / k : ℕ) : ℝ) := by positivity
  unfold rank
  constructor <;> nlinarith

/-- Cambie's sequence of length `k ^ 2`: `xᵢ = 1 + (rank k i + k ^ 2) / (2 k ^ 3)`. -/
noncomputable def cambie (k : ℕ) (i : Fin (k ^ 2)) : ℝ :=
  1 + (rank k i + (k : ℝ) ^ 2) / (2 * (k : ℝ) ^ 3)

/-- Cambie's sequence is ordered exactly like the rank. -/
theorem cambie_lt_iff {k : ℕ} (hk : 0 < k) (i j : Fin (k ^ 2)) :
    cambie k i < cambie k j ↔ rank k i < rank k j := by
  have : (0 : ℝ) < 2 * (k : ℝ) ^ 3 := by positivity
  unfold cambie
  constructor
  · intro h
    have := (div_lt_div_iff_of_pos_right this).mp (by linarith : (rank k i + (k : ℝ) ^ 2) / (2 * (k : ℝ) ^ 3) < (rank k j + (k : ℝ) ^ 2) / (2 * (k : ℝ) ^ 3))
    linarith
  · intro h
    have := (div_lt_div_iff_of_pos_right this).mpr (by linarith : rank k i + (k : ℝ) ^ 2 < rank k j + (k : ℝ) ^ 2)
    linarith

/-- All values of Cambie's sequence lie in `[1, 1 + 1/k]`. -/
theorem cambie_bounds {k : ℕ} (hk : 0 < k) (i : Fin (k ^ 2)) :
    1 ≤ cambie k i ∧ cambie k i ≤ 1 + 1 / (k : ℝ) := by
  obtain ⟨h1, h2⟩ := rank_bounds hk i.isLt
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have : (0 : ℝ) < 2 * (k : ℝ) ^ 3 := by positivity
  unfold cambie
  constructor
  · have : 0 ≤ (rank k i + (k : ℝ) ^ 2) / (2 * (k : ℝ) ^ 3) := div_nonneg h1 this.le
    linarith
  · have : (rank k i + (k : ℝ) ^ 2) / (2 * (k : ℝ) ^ 3) ≤ 1 / (k : ℝ) := by
      rw [div_le_div_iff₀ this hk']
      nlinarith
    linarith

/-- Cambie's sequence consists of distinct numbers. -/
theorem cambie_injective {k : ℕ} (hk : 0 < k) : Function.Injective (cambie k) := by
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rcases rank_cases hk (show (i : ℕ) < j from hlt) with ⟨_, h'⟩ | ⟨_, h'⟩
    · exact absurd h ((cambie_lt_iff hk i j).mpr h').ne
    · exact absurd h ((cambie_lt_iff hk j i).mpr h').ne'
  · rcases rank_cases hk (show (j : ℕ) < i from hlt) with ⟨_, h'⟩ | ⟨_, h'⟩
    · exact absurd h ((cambie_lt_iff hk j i).mpr h').ne'
    · exact absurd h ((cambie_lt_iff hk i j).mpr h').ne

/-- An increasing subsequence of Cambie's sequence has at most `k` terms. -/
theorem card_le_of_monotoneOn {k : ℕ} (hk : 0 < k) {I : Finset (Fin (k ^ 2))}
    (hI : MonotoneOn (cambie k) ↑I) : I.card ≤ k := by
  have aux : ∀ i ∈ I, ∀ j ∈ I, (i : ℕ) < j → (i : ℕ) % k ≠ (j : ℕ) % k := by
    intro i hi j hj hij hmod
    rcases rank_cases hk hij with ⟨hd, _⟩ | ⟨_, h'⟩
    · have := Nat.div_add_mod (i : ℕ) k
      have := Nat.div_add_mod (j : ℕ) k
      rw [hd, hmod] at *
      omega
    · have h1 := hI (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) (le_of_lt hij)
      have h2 := (cambie_lt_iff hk j i).mpr h'
      linarith
  have := Finset.card_le_card_of_injOn (fun i : Fin (k ^ 2) => (i : ℕ) % k) (t := Finset.range k)
    (fun i _ => Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hk))) (by
      intro i hi j hj h
      simp only at h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact aux i hi j hj hlt h
      · exact aux j hj i hi hlt h.symm)
  simpa using this

/-- A decreasing subsequence of Cambie's sequence has at most `k` terms. -/
theorem card_le_of_antitoneOn {k : ℕ} (hk : 0 < k) {I : Finset (Fin (k ^ 2))}
    (hI : AntitoneOn (cambie k) ↑I) : I.card ≤ k := by
  have aux : ∀ i ∈ I, ∀ j ∈ I, (i : ℕ) < j → (i : ℕ) / k ≠ (j : ℕ) / k := by
    intro i hi j hj hij hdiv
    rcases rank_cases hk hij with ⟨_, h'⟩ | ⟨hd, _⟩
    · have h1 := hI (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) (le_of_lt hij)
      have h2 := (cambie_lt_iff hk i j).mpr h'
      linarith
    · omega
  have := Finset.card_le_card_of_injOn (fun i : Fin (k ^ 2) => (i : ℕ) / k) (t := Finset.range k)
    (fun i _ => Finset.mem_coe.mpr (Finset.mem_range.mpr (by
      rw [Nat.div_lt_iff_lt_mul hk]
      have := i.isLt
      nlinarith))) (by
      intro i hi j hj h
      simp only at h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact aux i hi j hj hlt h
      · exact aux j hj i hi hlt h.symm)
  simpa using this

/-- Every monotone subsequence sum of Cambie's sequence is at most `k + 1`. -/
theorem sum_le {k : ℕ} (hk : 0 < k) {S : ℝ}
    (hS : S ∈ Erdos1026.monotonicSubsequenceSums (cambie k)) : S ≤ k + 1 := by
  obtain ⟨I, hI, rfl⟩ := hS
  have hcard : I.card ≤ k := hI.elim (card_le_of_monotoneOn hk) (card_le_of_antitoneOn hk)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  calc ∑ i ∈ I, cambie k i ≤ ∑ _i ∈ I, (1 + 1 / (k : ℝ)) :=
        Finset.sum_le_sum fun i _ => (cambie_bounds hk i).2
    _ = (I.card : ℝ) * (1 + 1 / (k : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * (1 + 1 / (k : ℝ)) := by gcongr
    _ = k + 1 := by field_simp

/-- The total sum of Cambie's sequence is at least `k ^ 2`. -/
theorem total_ge {k : ℕ} (hk : 0 < k) : (k : ℝ) ^ 2 ≤ ∑ i, cambie k i := by
  calc (k : ℝ) ^ 2 = ∑ _i : Fin (k ^ 2), (1 : ℝ) := by simp
    _ ≤ ∑ i, cambie k i := Finset.sum_le_sum fun i _ => (cambie_bounds hk i).1

/-- No constant `c > 1` is admissible: `1` is an upper bound of `admissibleConstants`. -/
theorem upper_bound : type_of% @Erdos1026.erdos_1026.variants.upper_bound := by
  intro c hc
  by_contra hnot
  have hlt : 1 < c := not_le.mp hnot
  set δ : ℝ := (c - 1) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hc δ hδpos)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  set k : ℕ := max (max N m) 1 with hkdef
  have hk : 0 < k := by omega
  have hkN : N ≤ k ^ 2 := by
    have : k ≤ k ^ 2 := by nlinarith
    omega
  have hkm : (m : ℝ) ≤ k := by exact_mod_cast (show m ≤ k by omega)
  obtain ⟨S, hS, hle⟩ := hN (k ^ 2) hkN (cambie k) (cambie_injective hk)
    (fun i => lt_of_lt_of_le one_pos (cambie_bounds hk i).1)
  have hS' := sum_le hk hS
  have htot := total_ge hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hsqrt : Real.sqrt ((k ^ 2 : ℕ) : ℝ) = k := by
    push_cast
    exact Real.sqrt_sq hk'.le
  rw [hsqrt] at hle
  have hce : c - δ = 1 + δ := by rw [hδ]; ring
  rw [hce] at hle
  have h1 : (1 + δ) / (k : ℝ) * (k : ℝ) ^ 2 ≤ (1 + δ) / (k : ℝ) * ∑ i, cambie k i := by
    gcongr
  have h2 : (1 + δ) / (k : ℝ) * (k : ℝ) ^ 2 = (1 + δ) * k := by
    field_simp
  have h3 : 1 < δ * k := by
    have := (div_lt_iff₀ hδpos).mp hm
    nlinarith
  nlinarith

end Math0.Erdos1026

#math0_proves Math0.Erdos1026.upper_bound Erdos1026.erdos_1026.variants.upper_bound
