/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1148»
import Math0.Audit

/-!
# Erdős Problem 1148: the weaker variant with bound `n + 2√n`

Erdős Problem 1148 asks whether every large `n` is `x² + y² - z²` with `max(x², y², z²) ≤ n`;
the booklet [Va99] remarks that this is "obvious" if the bound `n` is relaxed to `n + 2√n`.
We prove this relaxed statement, `Erdos1148.erdos_1148.variants.weaker`, for every natural
number `n`. Writing `n = s² + d` with `s = ⌊√n⌋` and `0 ≤ d ≤ 2s`, we take `(s, 0, 0)` if
`d = 0`, `(s, t + 1, t)` if `d = 2t + 1`, and `(s + 1, s - t, s - t + 1)` if `d = 2t ≥ 2`;
in each case the identity is elementary algebra, all squares other than `(s + 1)²` are at most
`s² ≤ n`, and `(s + 1)² ≤ n + 2s ≤ n + 2√n` because `n ≥ s² + 2` in the last case.
-/

namespace Math0.Erdos1148

/-- Arithmetic core: if `s² ≤ n < (s + 1)²` then `n = x² + y² - z²` with all of
`x², y², z²` at most `n + 2s`. -/
lemma exists_rep_of_sqrt_bounds (s n : ℕ) (h1 : s * s ≤ n) (h2 : n < (s + 1) * (s + 1)) :
    ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n + 2 * s ∧ y ^ 2 ≤ n + 2 * s ∧
      z ^ 2 ≤ n + 2 * s := by
  obtain ⟨d, rfl⟩ : ∃ d, n = s * s + d := ⟨n - s * s, by omega⟩
  have hd : d ≤ 2 * s := by nlinarith
  obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' d
  · subst ht
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · refine ⟨s, 0, 0, ?_, ?_, ?_, ?_⟩
      · ring_nf; omega
      · nlinarith
      · nlinarith
      · nlinarith
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (show t ≤ s by omega)
      refine ⟨t + u + 1, u, u + 1, ?_, ?_, ?_, ?_⟩
      · have e : (t + u + 1) ^ 2 + u ^ 2 = (t + u) * (t + u) + 2 * t + (u + 1) ^ 2 := by ring
        omega
      · nlinarith
      · nlinarith
      · nlinarith
  · subst ht
    refine ⟨s, t + 1, t, ?_, ?_, ?_, ?_⟩
    · have e : s ^ 2 + (t + 1) ^ 2 = s * s + (2 * t + 1) + t ^ 2 := by ring
      omega
    · nlinarith
    · have : t + 1 ≤ s := by omega
      nlinarith
    · nlinarith

/-- Transfer a natural-number bound `m ≤ n + 2⌊√n⌋` to the real bound `m ≤ n + 2√n`. -/
lemma cast_le_add_two_sqrt {m n : ℕ} (h : m ≤ n + 2 * Nat.sqrt n) :
    (m : ℝ) ≤ n + 2 * Real.sqrt n := by
  have hs : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hc : (m : ℝ) ≤ (n : ℝ) + 2 * ((Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast h
  linarith

/-- Every natural number `n` can be written as `n = x² + y² - z²` with
`max(x², y², z²) ≤ n + 2√n`. -/
theorem erdos_1148_weaker : type_of% @Erdos1148.erdos_1148.variants.weaker := by
  intro n
  obtain ⟨x, y, z, h, hx, hy, hz⟩ :=
    exists_rep_of_sqrt_bounds (Nat.sqrt n) n (Nat.sqrt_le n) (Nat.lt_succ_sqrt n)
  refine ⟨x, y, z, h, ?_, ?_, ?_⟩
  · exact_mod_cast cast_le_add_two_sqrt hx
  · exact_mod_cast cast_le_add_two_sqrt hy
  · exact_mod_cast cast_le_add_two_sqrt hz

end Math0.Erdos1148

#math0_proves Math0.Erdos1148.erdos_1148_weaker Erdos1148.erdos_1148.variants.weaker
