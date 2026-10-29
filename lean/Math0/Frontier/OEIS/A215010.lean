/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A215010
import Math0.Audit

/-!
# An equiangular decagon with sides in arithmetic progression (A215010)

We refute Garcia's conjecture that hexagons are the only equiangular simple convex polygons whose
integer side lengths are the terms of an arithmetic progression in some order.

Counterexample: `N = 10`, `t = d = 1`, with consecutive sides `(1, 4, 5, 8, 9, 2, 3, 6, 7, 10)`,
i.e. `σ = (0, 3, 4, 7, 8, 1, 2, 5, 6, 9)`. Let `ζ = exp (2πi/10)`, a primitive `10`th root of
unity, so `edgeDir 10 k = ζ ^ k`. Then `ζ ^ 5 = -1` and `ζ ≠ -1`, so from
`ζ ^ 5 + 1 = (ζ + 1) (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1)` we get `Φ₁₀(ζ) = ζ⁴ - ζ³ + ζ² - ζ + 1 = 0`.
Using `ζ ^ (k + 5) = -ζ ^ k`, the closing sum is
`∑_{k<5} (s k - s (k+5)) ζ ^ k = -1 + ζ - ζ² + ζ³ - ζ⁴ = -Φ₁₀(ζ) = 0`.
-/

namespace Math0.Frontier.A215010
open Math0.Statements.A215010

/-- The ordering `σ = (0, 3, 4, 7, 8, 1, 2, 5, 6, 9)` of `Fin 10`, with its explicit inverse. -/
private def σ10 : Equiv.Perm (Fin 10) where
  toFun := ![0, 3, 4, 7, 8, 1, 2, 5, 6, 9]
  invFun := ![0, 5, 6, 1, 2, 7, 8, 3, 4, 9]
  left_inv := by decide
  right_inv := by decide

/-- `ζ = exp (2πi/10)` satisfies `Φ₁₀(ζ) = ζ⁴ - ζ³ + ζ² - ζ + 1 = 0` and `ζ ^ 5 = -1`. -/
private theorem zeta_props :
    edgeDir 10 1 ^ 4 - edgeDir 10 1 ^ 3 + edgeDir 10 1 ^ 2 - edgeDir 10 1 + 1 = 0 ∧
      edgeDir 10 1 ^ 5 = -1 := by
  have hz : IsPrimitiveRoot (edgeDir 10 1) 10 := by
    have := Complex.isPrimitiveRoot_exp 10 (by norm_num)
    unfold edgeDir
    convert this using 2
    push_cast; ring
  set ζ := edgeDir 10 1
  have h5 : ζ ^ 5 = -1 := by
    have h2 : IsPrimitiveRoot (ζ ^ 5) (10 / 5) := hz.pow_of_dvd (by norm_num) (by norm_num)
    exact IsPrimitiveRoot.eq_neg_one_of_two_right h2
  have hne : ζ + 1 ≠ 0 := by
    intro h
    have : ζ = -1 := by linear_combination h
    have h2 : ζ ^ 2 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    exact h2 (by rw [this]; norm_num)
  refine ⟨?_, h5⟩
  have hprod : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by
    linear_combination h5
  exact (mul_eq_zero.mp hprod).resolve_left hne

/-- `edgeDir 10 k = ζ ^ k` with `ζ = edgeDir 10 1`. -/
private theorem edgeDir_ten (k : ℕ) : edgeDir 10 k = edgeDir 10 1 ^ k := by
  unfold edgeDir
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- The decagon with sides `(1, 4, 5, 8, 9, 2, 3, 6, 7, 10)` is equiangular. -/
private theorem decagon : IsEquiangularPolygon 10 (fun k => 1 + (σ10 k : ℕ) * 1) := by
  refine ⟨by norm_num, fun _ => by positivity, ?_⟩
  obtain ⟨hΦ, h5⟩ := zeta_props
  rw [Finset.sum_congr rfl fun k _ => by rw [edgeDir_ten]]
  set ζ := edgeDir 10 1
  simp [Fin.sum_univ_succ, σ10]
  have h6 : ζ ^ 6 = -ζ := by linear_combination ζ * h5
  have h7 : ζ ^ 7 = -ζ ^ 2 := by linear_combination ζ ^ 2 * h5
  have h8 : ζ ^ 8 = -ζ ^ 3 := by linear_combination ζ ^ 3 * h5
  have h9 : ζ ^ 9 = -ζ ^ 4 := by linear_combination ζ ^ 4 * h5
  norm_num
  linear_combination (-1 : ℂ) * hΦ + 2 * h5 + 3 * h6 + 6 * h7 + 7 * h8 + 10 * h9

/-- Garcia's conjecture fails: the equiangular decagon with sides `1, …, 10` in the order
`(1, 4, 5, 8, 9, 2, 3, 6, 7, 10)` has `N = 10 ≠ 6`. -/
theorem result : ¬ statement := by
  intro h
  have := h 10 1 1 le_rfl σ10 decagon
  norm_num at this

end Math0.Frontier.A215010

#math0_settles Math0.Frontier.A215010.result Math0.Statements.A215010.statement
