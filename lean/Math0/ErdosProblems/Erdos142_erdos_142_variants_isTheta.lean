/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«142»
import Math0.Audit

/-!
# Erdős Problem 142 (order of magnitude variant): no single answer works for all `k`

Erdős Problem 142 asks for the order of magnitude of `r_k(N)`, the largest size of a subset of
`{1, …, N}` with no non-trivial `k`-term arithmetic progression. The upstream statement
`erdos_142.variants.isTheta` asks for one function `answer : ℕ → ℝ`, *independent of `k`*, with
`r_k =Θ answer` for every `k`. We prove that no such function exists, whatever the value of the
unknown `answer`. Indeed `r_1(N) = N`, while `r_2(N) ≤ 1` because any two distinct elements
form a 2-term progression; `Θ`-equivalence is transitive and symmetric, so `N =O(1)`, which is
absurd. This is a formalization defect (the answer should depend on `k`), not progress on the
research problem.
-/

namespace Math0.Erdos142

open Asymptotics Filter

/-- A set of naturals that is free of non-trivial 2-term arithmetic progressions has at most
one element: two distinct elements `a < b` form the progression `{a, b}`. -/
theorem isTheta_card_le_one_of_free {S : Finset ℕ} (h : (S : Set ℕ).IsAPOfLengthFree 2) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have h1 := h {a, b} (by
      intro x hx; rcases hx with rfl | rfl <;> simpa using (by assumption))
      (Nat.isAPOfLength_pair hlt)
    norm_num at h1
  · have h1 := h {b, a} (by
      intro x hx; rcases hx with rfl | rfl <;> simpa using (by assumption))
      (Nat.isAPOfLength_pair hlt)
    norm_num at h1

/-- `r_2(N) ≤ 1` for every `N`. -/
theorem isTheta_r_two_le_one (N : ℕ) : Erdos142.r 2 N ≤ 1 := by
  unfold Erdos142.r Set.IsAPOfLengthFree.maxCard
  apply csSup_le'
  rintro n ⟨S, _, hS, rfl⟩
  exact isTheta_card_le_one_of_free (by exact_mod_cast hS)

/-- For every candidate `answer : ℕ → ℝ`, it is false that `r_k =Θ answer` for all `k`
simultaneously (already `k = 1` and `k = 2` are incompatible). -/
theorem not_isTheta : ∀ a : ℕ → ℝ,
    ¬ ∀ k : ℕ, (fun N => (Erdos142.r k N : ℝ)) =Θ[atTop] a := by
  intro a h
  have h12 : (fun N => (Erdos142.r 1 N : ℝ)) =O[atTop] (fun N => (Erdos142.r 2 N : ℝ)) :=
    ((h 1).trans (h 2).symm).isBigO
  have h2b : (fun N => (Erdos142.r 2 N : ℝ)) =O[atTop] (fun _ => (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with N
    simp only [Real.norm_eq_abs, abs_one, mul_one, Nat.abs_cast]
    exact_mod_cast isTheta_r_two_le_one N
  have h3 := h12.trans h2b
  simp only [Erdos142.r, Set.IsAPOfLengthFree.maxCard_one] at h3
  rw [Asymptotics.isBigO_one_iff] at h3
  exact Filter.not_isBoundedUnder_of_tendsto_atTop
    (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop) h3

end Math0.Erdos142

#math0_refutes_every_answer Math0.Erdos142.not_isTheta Erdos142.erdos_142.variants.isTheta with Erdos142.erdos_142.variants.isTheta.answer
