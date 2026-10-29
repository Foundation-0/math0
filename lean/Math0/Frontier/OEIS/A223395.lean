/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A223395
import Math0.Audit

/-!
# A223395: walks on the 4 × 4 grid graph satisfy a third-order recurrence

We prove all three conjectures recorded in the entry: Hardin's recurrence
`a(n) = 3a(n-1) + 2a(n-2) - 4a(n-3)` (`n ≥ 4`), Barker's generating function and Barker's
closed form.

Let `c n` be the vector `v ↦ cnt n v` (walks with `n + 1` vertices starting at `v`), so
`c (n+1) = A c n` for the adjacency matrix `A` of the grid graph, `c 0 = 1`, and
`a (n+1) = ∑ v, c n v`. The key fact is the vector identity `A³1 + 4·1 = 3A²1 + 2A1`, i.e.
`c 3 + 4 c 0 = 3 c 2 + 2 c 1`, which is checked in the kernel on the list computation `colsL`.
Applying `A` (linearity of `cnt_succ`) propagates it to `c (n+3) + 4 c n = 3 c (n+2) + 2 c (n+1)`
for all `n`, and summing over the top vertex gives `a(m+4) + 4a(m+1) = 3a(m+3) + 2a(m+2)`.
The generating function follows by comparing coefficients of
`(1 - 3X - 2X² + 4X³) ∑_{n≥1} a(n) Xⁿ`, and the closed form by induction, since `1`, `1 ± √5`
are the roots of `x³ - 3x² - 2x + 4 = (x - 1)(x² - 2x - 4)` and the formula matches
`a(1), a(2), a(3) = 16, 48, 152`.
-/

namespace Math0.Frontier.A223395
open Math0.Statements.A223395

/-- `cnt n v` read off the fast list computation. -/
private theorem cnt_eq_colsL (n : ℕ) (v : Fin 16) : cnt n v = (colsL n).getD v.val 0 := by
  rw [colsL_eq, getD_map_finRange]

/-- Base case of the vector recurrence (kernel-checked). -/
private theorem cnt_base : ∀ v : Fin 16, cnt 3 v + 4 * cnt 0 v = 3 * cnt 2 v + 2 * cnt 1 v := by
  simp only [cnt_eq_colsL]
  decide +kernel

/-- The vector recurrence `A^3 c = 3 A^2 c + 2 A c - 4 c`, propagated by linearity. -/
private theorem cnt_rec (n : ℕ) :
    ∀ v : Fin 16, cnt (n + 3) v + 4 * cnt n v = 3 * cnt (n + 2) v + 2 * cnt (n + 1) v := by
  induction n with
  | zero => exact cnt_base
  | succ n ih =>
    intro v
    rw [cnt_succ (n + 3) v, cnt_succ n v, cnt_succ (n + 2) v, cnt_succ (n + 1) v,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : Adj v u
    · simp only [if_pos h]
      exact ih u
    · simp [h]

/-- Hardin's recurrence in `ℕ`, without subtraction. -/
private theorem a_rec (m : ℕ) : a (m + 4) + 4 * a (m + 1) = 3 * a (m + 3) + 2 * a (m + 2) := by
  rw [a_succ (m + 3), a_succ m, a_succ (m + 2), a_succ (m + 1), Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => cnt_rec m v

/-- Hardin's recurrence. -/
private theorem rec_part : statementRec := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h := congrArg (Nat.cast : ℕ → ℤ) (a_rec m)
  push_cast at h
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  linarith

/-- The first three terms. -/
private theorem a_small : a 1 = 16 ∧ a 2 = 48 ∧ a 3 = 152 := by
  simp only [a_eq_aL]
  decide +kernel

/-- Barker's generating function, by comparing coefficients. -/
private theorem gf_part : statementGF := by
  unfold statementGF
  have hL : ∀ F : PowerSeries ℤ,
      (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C (3 : ℤ) * (PowerSeries.X ^ 1 * F)
        - PowerSeries.C (2 : ℤ) * (PowerSeries.X ^ 2 * F)
        + PowerSeries.C (4 : ℤ) * (PowerSeries.X ^ 3 * F) := by
    intro F
    simp only [map_ofNat]
    ring
  have hR : (8 : PowerSeries ℤ) * PowerSeries.X * (2 - 3 * PowerSeries.X ^ 2) =
      PowerSeries.C (16 : ℤ) * PowerSeries.X ^ 1 - PowerSeries.C (24 : ℤ) * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [hL, hR]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_mk]
  rcases k with _ | _ | _ | _ | k
  · simp
  · simp [a_small.1]
  · simp [a_small.1, a_small.2.1]
  · simp [a_small.1, a_small.2.1, a_small.2.2]
  · have h := congrArg (Nat.cast : ℕ → ℤ) (a_rec k)
    push_cast at h
    simp
    linarith

/-- Barker's closed form, by induction using the recurrence. -/
private theorem cf_part : statementClosedForm := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set s := Real.sqrt 5
  have hs : s ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have key : ∀ m : ℕ,
      (a (m + 1) : ℝ) = (8 + (11 - 5 * s) * (1 - s) ^ (m + 1) + (1 + s) ^ (m + 1) * (11 + 5 * s)) / 5 ∧
      (a (m + 2) : ℝ) = (8 + (11 - 5 * s) * (1 - s) ^ (m + 2) + (1 + s) ^ (m + 2) * (11 + 5 * s)) / 5 ∧
      (a (m + 3) : ℝ) = (8 + (11 - 5 * s) * (1 - s) ^ (m + 3) + (1 + s) ^ (m + 3) * (11 + 5 * s)) / 5 := by
    intro m
    induction m with
    | zero =>
      obtain ⟨h1, h2, h3⟩ := a_small
      simp only [h1, h2, h3]
      push_cast
      refine ⟨?_, ?_, ?_⟩
      · linear_combination (-2 : ℝ) * hs
      · linear_combination (-42 / 5 : ℝ) * hs
      · linear_combination (-(2 * s ^ 2 + 146 / 5) : ℝ) * hs
    | succ m ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨h2, h3, ?_⟩
      have h := congrArg (Nat.cast : ℕ → ℝ) (a_rec m)
      push_cast at h
      have e : (a (m + 1 + 3) : ℝ) = a (m + 4) := by rfl
      rw [e]
      linear_combination h - 4 * h1 + 3 * h3 + 2 * h2
        + (((11 - 5 * s) * (1 - s) ^ (m + 1) * s - (11 + 5 * s) * (1 + s) ^ (m + 1) * s) / 5) * hs
  exact (key m).1

/-- All three conjectures of A223395 hold: Hardin's recurrence, Barker's generating function and
Barker's closed form. -/
theorem result : statement := ⟨rec_part, gf_part, cf_part⟩

end Math0.Frontier.A223395

#math0_settles Math0.Frontier.A223395.result Math0.Statements.A223395.statement
