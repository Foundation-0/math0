/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«319»
import Math0.Audit

/-!
# Erdős Problem 319: the constant-answer formulation is refuted

Erdős Problem 319 asks for `c(N)`, the largest size of `A ⊆ {1, …, N}` that carries signs
`δ : A → {-1, 1}` with `∑_{n ∈ A} δ(n)/n = 0` while no nonempty proper subset of `A` has signed
sum zero. The upstream statement `erdos_319` uses one unknown `erdos_319.answer : ℕ` that does not
depend on `N`, while quantifying over every `N`. We prove that no natural number works: for `N = 0`
only `A = ∅` is allowed, so the maximum is `0`, while for `N = 6` the set `{2, 3, 6}` with
`1/2 - 1/3 - 1/6 = 0` is admissible, so the maximum is at least `3`. This is a defect of the
formalization (the intended answer depends on `N`, see the upstream `isTheta` variant), not a
resolution of the mathematical problem.
-/

open scoped Finset

namespace Math0.Erdos319

/-- The sign pattern `+1` at `2` and `-1` elsewhere, used on `{2, 3, 6}`. -/
def δ₀ : ℕ → ℤˣ := fun n => if n = 2 then 1 else -1

/-- `1/2 - 1/3 - 1/6 = 0`. -/
theorem sum_witness : ∑ n ∈ ({2, 3, 6} : Finset ℕ), (δ₀ n : ℚ) / n = 0 := by
  simp [δ₀, Finset.sum_insert]
  norm_num

/-- No nonempty proper subset of `{2, 3, 6}` has signed reciprocal sum zero under `δ₀`. -/
theorem proper_witness : ∀ A' ⊂ ({2, 3, 6} : Finset ℕ), A'.Nonempty →
    ∑ n ∈ A', (δ₀ n : ℚ) / n ≠ 0 := by
  intro A' hA' hne
  have hmem : A' ∈ (({2, 3, 6} : Finset ℕ).powerset.erase {2, 3, 6}) := by
    rw [Finset.mem_erase, Finset.mem_powerset]
    exact ⟨hA'.ne, hA'.subset⟩
  have hpow : (({2, 3, 6} : Finset ℕ).powerset.erase {2, 3, 6}) =
      {∅, {2}, {3}, {6}, {2, 3}, {2, 6}, {3, 6}} := by decide
  rw [hpow] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp at hne
  all_goals simp [δ₀, Finset.sum_insert]
  all_goals norm_num

/-- For `N = 6`, the size `3` is attained (by `A = {2, 3, 6}`). -/
theorem three_mem : 3 ∈ { #A | (A) (_ : A ⊆ Finset.Icc 1 6)
      (_ : ∃ δ : ℕ → ℤˣ, ∑ n ∈ A, (δ n : ℚ) / n = 0 ∧
        ∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) } :=
  ⟨{2, 3, 6}, by decide, ⟨δ₀, sum_witness, proper_witness⟩, by decide⟩

/-- For `N = 0`, the only attainable size is `0`, since `A ⊆ Icc 1 0 = ∅`. -/
theorem eq_zero_of_mem {c : ℕ} (hc : c ∈ { #A | (A) (_ : A ⊆ Finset.Icc 1 0)
      (_ : ∃ δ : ℕ → ℤˣ, ∑ n ∈ A, (δ n : ℚ) / n = 0 ∧
        ∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) }) : c = 0 := by
  obtain ⟨A, hA, -, rfl⟩ := hc
  have : A = ∅ := by
    simpa using hA
  simp [this]

/-- No single natural number `c` is the maximum size of an admissible set for every `N`. -/
theorem erdos_319_refuted : ∀ c : ℕ, ¬ ∀ N : ℕ, IsGreatest
    { #A | (A) (_ : A ⊆ Finset.Icc 1 N)
      (_ : ∃ δ : ℕ → ℤˣ, ∑ n ∈ A, (δ n : ℚ) / n = 0 ∧
        ∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) } c := by
  intro c h
  have h0 : c = 0 := eq_zero_of_mem (h 0).1
  have h6 : 3 ≤ c := (h 6).2 three_mem
  omega

end Math0.Erdos319

#math0_refutes_every_answer Math0.Erdos319.erdos_319_refuted Erdos319.erdos_319 with
  Erdos319.erdos_319.answer
