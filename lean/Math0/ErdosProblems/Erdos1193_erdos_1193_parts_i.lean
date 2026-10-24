/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1193»
import Math0.Audit

/-!
# Erdős Problem 1193 (i): the lower density need not vanish

Erdős [Er80] asked whether, for every `A ⊆ ℕ` and every non-decreasing positive `g : ℕ → ℕ`, the
set `{n : 1_A ∗ 1_A(n) = g(n)}` always has lower density `0`. As recorded on
erdosproblems.com, the answer as stated is trivially no, and this file proves the upstream
statement `Erdos1193.erdos_1193.parts.i` (the negation of the universal claim). The
counterexample is `A = ℕ`, `g n = n + 1`: every `n` has exactly `n + 1` ordered representations
`n = a + b` with `a, b ∈ ℕ`, so the set in question is all of `ℕ`, whose lower density is `1`.
-/

namespace Math0.Erdos1193

open AdditiveCombinatorics

/-- With `A = ℕ`, the representation function is `n ↦ n + 1`. -/
theorem sumRep_univ_eq (n : ℕ) : sumRep (Set.univ : Set ℕ) n = n + 1 := by
  simp

/-- The set of all natural numbers has lower density `1`. -/
theorem lowerDensity_univ : (Set.univ : Set ℕ).lowerDensity = 1 := by
  exact (Set.HasDensity.univ (β := ℕ)).liminf_eq

/-- Not every set `{n | sumRep A n = g n}` with `g` monotone and positive has lower density `0`:
`A = ℕ`, `g n = n + 1` is a counterexample. -/
theorem erdos_1193_parts_i : type_of% @Erdos1193.erdos_1193.parts.i := by
  intro h
  have hmono : Monotone (fun n : ℕ => n + 1) := fun a b hab => Nat.succ_le_succ hab
  have hpos : ∀ n : ℕ, 0 < (fun n : ℕ => n + 1) n := fun n => Nat.succ_pos n
  have h0 := h Set.univ (fun n => n + 1) hmono hpos
  have hset : {n : ℕ | sumRep Set.univ n = n + 1} = Set.univ :=
    Set.eq_univ_of_forall fun n => sumRep_univ_eq n
  rw [hset, lowerDensity_univ] at h0
  exact one_ne_zero h0

end Math0.Erdos1193

#math0_proves Math0.Erdos1193.erdos_1193_parts_i Erdos1193.erdos_1193.parts.i
