/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Arxiv.«2602.05192».FirstProof4
import Math0.Audit

/-!
# First Proof, Problem 4 in degree 2: the finite free Stam inequality is an equality

Problem 4 of *First Proof* (arXiv:2602.05192) asks whether
`1 / Φ_n(p ⊞_n q) ≥ 1 / Φ_n(p) + 1 / Φ_n(q)` for monic real-rooted polynomials `p, q` of
degree `n`, where `⊞_n` is the finite additive convolution and `Φ_n` is the sum of squared
"Coulomb forces" between the roots (`∞` when there is a repeated root). We prove the upstream
statement `four_2`, the case `n = 2`. Writing `p = (X - a)(X - b)` and `q = (X - c)(X - d)`, a
direct computation gives `p ⊞_2 q = X² - sX + t` with `s = a + b + c + d` and
`t = ab + cd + (a + b)(c + d)/2`, whose discriminant is `(a - b)² + (c - d)²`: discriminants
add. Since `1 / Φ_2((X - x)(X - y)) = (x - y)² / 2` (also when `x = y`, where both sides are `0`),
the inequality holds with equality.
-/

open Polynomial Finset ENNReal Arxiv.«2602.05192»

namespace Math0.Arxiv.«2602.05192»

/-- The roots of `(X - x)(X - y)` are `{x, y}`. -/
lemma roots_quad (x y : ℝ) : ((X - C x) * (X - C y)).roots = {x, y} := by
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero x) (X_sub_C_ne_zero y))]
  simp [roots_X_sub_C]

/-- For a monic quadratic with roots `x, y`, `1 / Φ = (x - y)² / 2`. This includes the case of
a double root, where `Φ = ⊤` and both sides vanish. -/
lemma inv_Φ_quad (x y : ℝ) :
    1 / Φ ((X - C x) * (X - C y)) = ENNReal.ofReal ((x - y) ^ 2 / 2) := by
  unfold Φ
  rw [roots_quad]
  by_cases h : x = y
  · subst h
    simp
  · have hnd : ({x, y} : Multiset ℝ).Nodup := by simp [h]
    rw [if_pos hnd]
    have hxy : x - y ≠ 0 := sub_ne_zero.mpr h
    have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hts : ({x, y} : Multiset ℝ).toFinset = {x, y} := by
      ext z; simp
    simp only [hts]
    rw [Finset.sum_pair h]
    have e1 : ({x, y} : Finset ℝ).erase x = {y} := by
      ext z; simp; aesop
    have e2 : ({x, y} : Finset ℝ).erase y = {x} := by
      ext z; simp; aesop
    rw [e1, e2]
    simp only [Finset.sum_singleton]
    have hpos : 0 < (x - y) ^ 2 / 2 := by positivity
    have : (1 / (x - y)) ^ 2 + (1 / (y - x)) ^ 2 = ((x - y) ^ 2 / 2)⁻¹ := by
      field_simp
      ring
    rw [this, one_div]
    change (ENNReal.ofReal _)⁻¹ = _
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_inv]

/-- A monic real polynomial of degree 2 with two roots (counted with multiplicity) splits as
`(X - a)(X - b)`. -/
lemma quad_eq (p : ℝ[X]) (hd : p.degree = (2 : ℕ)) (hr : p.roots.card = 2) (hm : p.Monic) :
    ∃ a b, p = (X - C a) * (X - C b) := by
  have hnat : p.natDegree = 2 := natDegree_eq_of_degree_eq_some hd
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by rw [hr, hnat])
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hr
  refine ⟨a, b, ?_⟩
  rw [← h, hab]
  simp

/-- The finite additive convolution `⊞_2` of `(X - a)(X - b)` and `(X - c)(X - d)`. -/
lemma conv_eq (a b c d : ℝ) :
    finiteAdditiveConvolution 2 ((X - C a) * (X - C b)) ((X - C c) * (X - C d)) =
      X ^ 2 - C (a + b + c + d) * X + C (a * b + c * d + (a + b) * (c + d) / 2) := by
  have hp : ∀ x y : ℝ, (X - C x) * (X - C y) = X ^ 2 + C (-(x + y)) * X + C (x * y) := by
    intro x y
    simp only [map_neg, map_add, map_mul]
    ring
  have c0 : ∀ x y : ℝ, ((X - C x) * (X - C y)).coeff 0 = x * y := by
    intro x y; rw [hp]; simp
  have c1 : ∀ x y : ℝ, ((X - C x) * (X - C y)).coeff 1 = -(x + y) := by
    intro x y; rw [hp]; simp [coeff_C]
  have c2 : ∀ x y : ℝ, ((X - C x) * (X - C y)).coeff 2 = 1 := by
    intro x y; rw [hp]; simp
  simp only [finiteAdditiveConvolution, sum_range_succ, sum_range_zero]
  simp [Finset.Nat.antidiagonal_succ, c0, c1, c2, Nat.factorial]
  simp only [smul_eq_C_mul, div_eq_mul_inv, map_add, map_neg, map_mul, mul_one]
  ring

/-- A monic real quadratic `X² - sX + t` with nonnegative discriminant `r = s² - 4t` factors as
`(X - (s + √r)/2)(X - (s - √r)/2)`. -/
lemma quad_factor (s t r : ℝ) (hr : 0 ≤ r) (h : s ^ 2 - r = 4 * t) :
    X ^ 2 - C s * X + C t = (X - C ((s + √r) / 2)) * (X - C ((s - √r) / 2)) := by
  have h1 : (s + √r) / 2 + (s - √r) / 2 = s := by ring
  have h2 : (s + √r) / 2 * ((s - √r) / 2) = t := by
    have := Real.sq_sqrt hr
    linear_combination (-1/4 : ℝ) * this + (1/4 : ℝ) * h
  calc X ^ 2 - C s * X + C t
      = X ^ 2 - C ((s + √r) / 2 + (s - √r) / 2) * X + C ((s + √r) / 2 * ((s - √r) / 2)) := by
        rw [h1, h2]
    _ = (X - C ((s + √r) / 2)) * (X - C ((s - √r) / 2)) := by
        simp only [map_add, map_mul]
        ring

/-- For monic real-rooted quadratics `p, q`, `1/Φ₂(p) + 1/Φ₂(q) ≤ 1/Φ₂(p ⊞₂ q)`
(in fact with equality). -/
theorem four_2 : type_of% @Arxiv.«2602.05192».four_2 := by
  intro p q hpd hpr hqd hqr hpm hqm
  obtain ⟨a, b, rfl⟩ := quad_eq p hpd hpr hpm
  obtain ⟨c, d, rfl⟩ := quad_eq q hqd hqr hqm
  have hD : 0 ≤ (a - b) ^ 2 + (c - d) ^ 2 := by positivity
  rw [conv_eq, quad_factor (a + b + c + d) _ ((a - b) ^ 2 + (c - d) ^ 2) hD (by ring),
    inv_Φ_quad, inv_Φ_quad, inv_Φ_quad, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply le_of_eq
  congr 1
  have : (√((a - b) ^ 2 + (c - d) ^ 2)) ^ 2 = (a - b) ^ 2 + (c - d) ^ 2 := Real.sq_sqrt hD
  linear_combination (-1/2 : ℝ) * this

end Math0.Arxiv.«2602.05192»

#math0_proves Math0.Arxiv.«2602.05192».four_2 Arxiv.«2602.05192».four_2
