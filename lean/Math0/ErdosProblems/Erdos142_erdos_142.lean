/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«142»
import Math0.Audit

/-!
# Erdős Problem 142: the uniform asymptotic formula is refuted

Erdős Problem 142 asks for an asymptotic formula `f_k` with `r_k(N) ~ f_k(N)`, where `r_k(N)` is
the largest size of a subset of `{1, …, N}` with no non-trivial `k`-term arithmetic progression.
The upstream formalization uses a single unknown `erdos_142.answer : ℕ → ℝ` that does not depend
on `k`, while quantifying over every `k`. We prove that no choice of this function works:
`r_1(N) = N` (every set is free of 1-term progressions) while `r_2(N) ≤ 1` (any two distinct
elements form a 2-term progression), and these cannot both be asymptotic to the same function,
since that would force the bounded sequence `r_2(N)` to tend to infinity.
-/

namespace Math0.Erdos142

open Asymptotics Filter

/-- A set of naturals free of non-trivial 2-term progressions has at most one element. -/
theorem card_le_one_of_free_two {S : Finset ℕ} (hS : (S : Set ℕ).IsAPOfLengthFree 2) :
    S.card ≤ 1 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have hsub : ({a, b} : Set ℕ) ⊆ (S : Set ℕ) := by
      intro x hx
      rcases hx with rfl | rfl <;> simp_all
    have := hS _ hsub (Nat.isAPOfLength_pair hlt)
    norm_num at this
  · have hsub : ({b, a} : Set ℕ) ⊆ (S : Set ℕ) := by
      intro x hx
      rcases hx with rfl | rfl <;> simp_all
    have := hS _ hsub (Nat.isAPOfLength_pair hlt)
    norm_num at this

/-- `r_2(N) ≤ 1` for every `N`. -/
theorem r_two_le_one (N : ℕ) : Erdos142.r 2 N ≤ 1 := by
  show Set.IsAPOfLengthFree.maxCard 2 N ≤ 1
  unfold Set.IsAPOfLengthFree.maxCard
  apply csSup_le
  · refine ⟨0, ∅, Finset.empty_subset _, ?_, rfl⟩
    intro t ht hap
    have ht' : t = ∅ := Set.subset_empty_iff.1 (by simpa using ht)
    subst ht'
    exact absurd hap (Set.not_isAPOfLength_empty (by norm_num))
  · rintro n ⟨S, -, hS, rfl⟩
    exact card_le_one_of_free_two hS

/-- No single function `a : ℕ → ℝ` satisfies `r_k(N) ~ a(N)` for every `k`. -/
theorem erdos_142_refuted :
    ∀ a : ℕ → ℝ, ¬ ∀ k : ℕ, (fun N => (Erdos142.r k N : ℝ)) ~[atTop] a := by
  intro a h
  have h1 := h 1
  have h2 := h 2
  have h12 : (fun N => (Erdos142.r 1 N : ℝ)) ~[atTop] (fun N => (Erdos142.r 2 N : ℝ)) :=
    h1.trans h2.symm
  have htop1 : Tendsto (fun N => (Erdos142.r 1 N : ℝ)) atTop atTop := by
    have : (fun N => (Erdos142.r 1 N : ℝ)) = fun N : ℕ => (N : ℝ) := by
      funext N
      simp [Erdos142.r, Set.IsAPOfLengthFree.maxCard_one]
    rw [this]
    exact tendsto_natCast_atTop_atTop
  have htop2 := h12.tendsto_atTop htop1
  have hev := htop2.eventually_gt_atTop 1
  obtain ⟨N, hN⟩ := hev.exists
  have := r_two_le_one N
  have : (Erdos142.r 2 N : ℝ) ≤ 1 := by exact_mod_cast this
  linarith

end Math0.Erdos142

#math0_refutes_every_answer Math0.Erdos142.erdos_142_refuted Erdos142.erdos_142 with Erdos142.erdos_142.answer
