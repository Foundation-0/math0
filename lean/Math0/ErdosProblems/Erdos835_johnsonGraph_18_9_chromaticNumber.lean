/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«835»
import Math0.Audit

/-!
# Erdős Problem 835: the chromatic number of `J(18, 9)` exceeds `10`

Erdős Problem 835 asks whether the `k`-subsets of a `2k`-set can be coloured with `k + 1` colours
so that every `(k + 1)`-subset sees all colours; equivalently whether `χ(J(2k, k)) = k + 1`.
The upstream file records the case `k = 9`: `χ(J(18, 9)) > 10`. We prove it by first proving
Johnson's bound `α(J(n, k)) ≤ johnsonBound n 4 k` for the independence number (the upstream
lemma `indepNum_johnson_le_johnsonBound`, in full generality), via double counting: if `F` is a
family of `k`-subsets of `S` with pairwise intersections of size at most `k - 2`, then
`k * |F| = ∑_{i ∈ S} |{A ∈ F : i ∈ A}|`, and the sets `A \ {i}` with `i ∈ A ∈ F` form a family of
the same kind with parameters `(|S| - 1, k - 1)`. Evaluating gives `α(J(18, 9)) ≤ 4420`, hence
`χ(J(18, 9)) ≥ ⌈48620 / 4420⌉ = 11`.
-/

namespace Math0.Erdos835

open Finset SimpleGraph

/-- Johnson's bound for constant-weight codes of minimum distance `4`: a family `F` of `k`-subsets
of a finset `S` whose distinct members meet in at most `k - 2` elements has at most
`johnsonBound #S 4 k` members. -/
theorem card_le_johnsonBound {α : Type*} [DecidableEq α] :
    ∀ (k : ℕ) (S : Finset α) (F : Finset (Finset α)),
      (∀ A ∈ F, A ⊆ S ∧ #A = k) →
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → #(A ∩ B) + 1 < k) →
      #F ≤ Erdos835.johnsonBound #S 4 k := by
  intro k
  induction k with
  | zero =>
    intro S F hF _
    have hsub : F ⊆ {∅} := fun A hA => by
      simpa [← card_eq_zero] using (hF A hA).2
    calc #F ≤ 1 := (card_le_card hsub).trans (by simp)
      _ = _ := by cases #S <;> rfl
  | succ k ih =>
    intro S F hF hP
    have hle1 : k = 0 ∨ #S = 0 → #F ≤ 1 := by
      rintro (rfl | h0)
      · rw [card_le_one]
        intro A hA B hB
        by_contra hAB
        have := hP A hA B hB hAB
        omega
      · rw [card_eq_zero] at h0
        subst h0
        have hsub : F ⊆ {∅} := fun A hA => by
          simpa using (hF A hA).1
        exact (card_le_card hsub).trans (by simp)
    rcases hS : #S with _ | n
    · exact (hle1 (Or.inr hS)).trans (by rfl)
    by_cases hk : k = 0
    · subst hk
      exact (hle1 (Or.inl rfl)).trans (by simp [Erdos835.johnsonBound])
    rw [Erdos835.johnsonBound, if_neg (by omega), Nat.le_div_iff_mul_le (by omega)]
    -- each point lies in at most `johnsonBound n 4 k` members of `F`
    have h2 : ∀ i ∈ S, #{A ∈ F | i ∈ A} ≤ Erdos835.johnsonBound n 4 k := by
      intro i hi
      have hinj : Set.InjOn (fun A : Finset α => A.erase i) ({A ∈ F | i ∈ A} : Finset _) := by
        intro A hA B hB hAB
        simp only [coe_filter, Set.mem_ofPred_eq] at hA hB
        have := congrArg (insert i) hAB
        simpa [insert_erase hA.2, insert_erase hB.2] using this
      have := ih (S.erase i) (({A ∈ F | i ∈ A} : Finset _).image (fun A => A.erase i)) ?_ ?_
      · rwa [card_erase_of_mem hi, hS, card_image_of_injOn hinj] at this
      · simp only [mem_image, mem_filter]
        rintro _ ⟨A, ⟨hA, hiA⟩, rfl⟩
        refine ⟨erase_subset_erase _ (hF A hA).1, ?_⟩
        rw [card_erase_of_mem hiA, (hF A hA).2]
        rfl
      · simp only [mem_image, mem_filter]
        rintro _ ⟨A, ⟨hA, hiA⟩, rfl⟩ _ ⟨B, ⟨hB, hiB⟩, rfl⟩ hne
        have hAB : A ≠ B := fun h => hne (h ▸ rfl)
        have h1 := hP A hA B hB hAB
        have h3 : A.erase i ∩ B.erase i = (A ∩ B).erase i := by
          ext x; simp; tauto
        rw [h3, card_erase_of_mem (mem_inter.2 ⟨hiA, hiB⟩)]
        have h5 : 0 < #(A ∩ B) := card_pos.2 ⟨i, mem_inter.2 ⟨hiA, hiB⟩⟩
        omega
    -- double counting the incidences `i ∈ A`
    have h1 : ∑ t ∈ F, #(S ∩ t) ≤ #S * Erdos835.johnsonBound n 4 k := sum_card_inter_le h2
    have h4 : ∑ t ∈ F, #(S ∩ t) = #F * (k + 1) := by
      rw [sum_const_nat]
      intro t ht
      rw [inter_eq_right.2 (hF t ht).1, (hF t ht).2]
    rw [hS] at h1
    linarith

/-- Johnson's bound for the independence number of the Johnson graph:
`α(J(n, k)) ≤ johnsonBound n 4 k` (the upstream lemma `indepNum_johnson_le_johnsonBound`). -/
theorem indepNum_johnson_le : type_of% @Erdos835.indepNum_johnson_le_johnsonBound := by
  intro n k
  obtain ⟨s, hs⟩ := (J(n, k)).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  have h := card_le_johnsonBound k (univ : Finset (Fin n))
    (s.map (Function.Embedding.subtype _)) ?_ ?_
  · simpa using h
  · simp only [mem_map, Function.Embedding.subtype_apply]
    rintro _ ⟨a, -, rfl⟩
    exact ⟨subset_univ _, a.2⟩
  · simp only [mem_map, Function.Embedding.subtype_apply]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
    have hab : a ≠ b := fun h => hne (h ▸ rfl)
    have := hs.isIndepSet (mem_coe.2 ha) (mem_coe.2 hb) hab
    rcases not_johnson_adj_iff_lt.1 this with h | h
    · exact absurd h hab
    · exact h

/-- The Johnson bound evaluates to `4420` for `n = 18`, distance `4`, weight `9`. -/
theorem johnsonBound_18_4_9 : Erdos835.johnsonBound 18 4 9 = 4420 := by decide

/-- The chromatic number of the Johnson graph `J(18, 9)` is at least `11`, i.e. greater than
`9 + 1`. -/
theorem johnsonGraph_18_9_chromaticNumber :
    type_of% @Erdos835.johnsonGraph_18_9_chromaticNumber := by
  have hc := card_div_indepNum_le_chromaticNumber (G := J(18, 9))
  have hα : α(J(18, 9)) ≤ 4420 :=
    johnsonBound_18_4_9 ▸ indepNum_johnson_le (n := 18) (k := 9)
  have : Nonempty {s : Finset (Fin 18) // #s = 9} :=
    ⟨⟨(univ : Finset (Fin 18)).filter (fun i => i.val < 9), by decide⟩⟩
  have hpos : 0 < α(J(18, 9)) := indepNum_pos
  have hcard : Nat.card {s : Finset (Fin 18) // #s = 9} = 48620 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_finset_len]
    decide
  have h10 : 10 < ⌈(Nat.card {s : Finset (Fin 18) // #s = 9} / α(J(18, 9)) : ℚ≥0)⌉₊ := by
    rw [Nat.lt_ceil, hcard, lt_div_iff₀ (by exact_mod_cast hpos)]
    have : ((10 * α(J(18, 9)) : ℕ) : ℚ≥0) < ((48620 : ℕ) : ℚ≥0) := by
      exact_mod_cast (by omega)
    simpa using this
  show (10 : ℕ∞) < _
  exact lt_of_lt_of_le (by exact_mod_cast h10) hc

end Math0.Erdos835

#math0_proves Math0.Erdos835.johnsonGraph_18_9_chromaticNumber Erdos835.johnsonGraph_18_9_chromaticNumber
