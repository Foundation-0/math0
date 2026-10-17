/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1048»
import Math0.Audit

/-!
# Erdős Problem 1048: the bound `diam ≥ 2` is attained by `zⁿ`

Erdős, Herzog and Piranian [EHP58] showed that when all roots of a monic polynomial `f` lie in
`|z| ≤ r ≤ 1/2`, the component of `{z : |f(z)| ≤ 1}` containing `0` has diameter at least `2`.
We prove that this is best possible: for `f = Xⁿ` with `n ≥ 1`, the connected component of the
level set `{z : |zⁿ| ≤ 1}` containing `0` has (extended) diameter exactly `2`. The level set is
the closed unit disk, which is convex and hence preconnected, so it is its own connected
component; its diameter is at most `2` by the triangle inequality and at least `2` since it
contains `1` and `-1`.
-/

namespace Math0.Erdos1048

open Polynomial Erdos1043

/-- For `n ≥ 1`, the level set `{z : ‖zⁿ‖ ≤ 1}` is the closed unit disk. -/
theorem levelSet_X_pow (n : ℕ) (hn : 1 ≤ n) :
    levelSet ((X : ℂ[X]) ^ n) = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  simp only [levelSet, Set.mem_ofPred_eq, eval_pow, eval_X, norm_pow, Metric.mem_closedBall,
    dist_zero_right]
  exact pow_le_one_iff_of_nonneg (norm_nonneg z) (by omega)

/-- The closed unit disk in `ℂ` has extended diameter exactly `2`. -/
theorem ediam_closedBall_one :
    Metric.ediam (Metric.closedBall (0 : ℂ) 1) = 2 := by
  apply le_antisymm
  · apply Metric.ediam_le
    intro x hx y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hx hy
    rw [edist_dist]
    have : dist x y ≤ 2 := by
      calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le x y
        _ ≤ 2 := by linarith
    calc ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal this
      _ = 2 := by norm_num
  · have h1 : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by simp
    have h2 : (-1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by simp
    have := Metric.edist_le_ediam_of_mem h1 h2
    have he : edist (1 : ℂ) (-1) = 2 := by
      rw [edist_dist, dist_eq_norm]
      norm_num
    rwa [he] at this

/-- For every `n ≥ 1`, the connected component containing `0` of the level set
`{z : ‖zⁿ‖ ≤ 1}` has extended diameter exactly `2`. -/
theorem diam_ge_two_is_best : type_of% @Erdos1048.erdos_1048.variants.diam_ge_two_is_best := by
  intro n hn
  rw [levelSet_X_pow n hn, (convex_closedBall (0 : ℂ) 1).isPreconnected.connectedComponentIn
    (Metric.mem_closedBall_self zero_le_one)]
  exact ediam_closedBall_one

end Math0.Erdos1048

#math0_proves Math0.Erdos1048.diam_ge_two_is_best Erdos1048.erdos_1048.variants.diam_ge_two_is_best
