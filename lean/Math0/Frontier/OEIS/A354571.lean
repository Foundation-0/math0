/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A354571
import Math0.Audit

/-!
# Even and odd legs with odd prime factors `≡ 3 (mod 4)`: `a(n)/n → π` (A354571, A354570)

We prove Selle's conjecture (A354571, A354570): `a(n)/n → π` for the ordered even legs and for
the ordered odd legs (with multiplicity) of the primitive Pythagorean triangles whose odd prime
factors are all `≡ 3 (mod 4)`.

* **Counting.** Let `g(m) = 2^ω(m)` if `m` is odd with all prime factors `≡ 3 (mod 4)`, else
  `g(m) = 0`. Primitive triangles `(b, k, c)` with odd leg `k` correspond to coprime
  factorizations `k² = d e`, `d < e` (via `(b, c) ↦ (c - b, c + b)`); those with leg `2n`, `n`
  even, to coprime factorizations `n² = d e`, `d < e` (via `(b, c) ↦ ((c - b)/2, (c + b)/2)`);
  legs `≡ 2 (mod 4)` do not occur. Counting coprime factorizations (`2^ω(N)` ordered ones) gives
  `2 wO(k) + [k = 1] = g(k)`, `wE(4j) + [j = 1] = g(j)` for odd `j`, `wE(8i) = wE(4i)`, and
  `wE(k) = 0` unless `4 ∣ k`.
* **Dirichlet series.** `g` is multiplicative and `g * χ₄ = 1_odd` (checked on prime powers), so
  `L(g, s) L(s, χ₄) = L(s, χ₀)` for the trivial character `χ₀` mod `4`. Summing the identity and
  using that the partial sums of `χ₄` are `0` or `1` gives `∑_{N/2 < n ≤ N} g(n) ≤ N`, hence
  `∑_{n ≤ N} g(n) ≤ 2N`. Since `L(s, χ₄) ≠ 0` on `re s ≥ 1` (Mathlib) and `(s - 1) L(s, χ₀)` is
  entire with value `1/2` at `1`, the function `L(g, s)/s - c/(s - 1)` with
  `c = (1/2)/L(1, χ₄)` extends continuously to `re s ≥ 1` (a `dslope`). Pairing the terms of
  `L(σ, χ₄)` and using Leibniz' series with dominated convergence as `σ → 1⁺` gives
  `L(1, χ₄) = π/4`, so `c = 2/π`.
* **Tauberian theorem.** A Wiener–Ikehara theorem for nonnegative coefficients with linearly
  bounded partial sums, proved with the Fejér kernel. With `B(v) = e^{-v} ∑_{n ≤ e^v} g(n)`, the
  triangle `φ_L` and its Fourier transform `Φ_L(u) = 2 (1 - cos (L u))/(L u²) ≥ 0`, Fubini and
  `ε → 0⁺` give `∫ φ_L(t) G(1 + it) e^{iyt} dt = ∫_{v > 0} (B(v) - c) Φ_L(y - v) dv`, which tends
  to `0` as `y → ∞` by the Riemann–Lebesgue lemma. Monotonicity of the partial sums and the
  concentration of `Φ_L` as `L → ∞` then squeeze `B(y) → c`, i.e. `∑_{n ≤ N} g(n) ~ (2/π) N`.
* **Conclusion.** `numLE wO N = (S(N) - 1)/2 ~ N/π` with `S(N) = ∑_{n ≤ N} g(n)`, and
  `numLE wE N = E(⌊N/4⌋)` where `E(J) = ∑_i R(⌊J/2^i⌋) ~ (4/π) J` (dominated convergence,
  `R(M) = S(M) - [M ≥ 1]`), so also `numLE wE N ~ N/π`. Inverting the counting functions gives
  `a(n)/n → π` for both sequences.
-/

namespace Math0.Frontier.A354571

namespace Tauber

open MeasureTheory Filter Topology Complex Set

noncomputable section

/-- The triangle function `phi L t = max 0 (1 - |t| / L)`, supported on `[-L, L]`. -/
private def phi (L t : ℝ) : ℝ := max 0 (1 - |t| / L)

/-- The Fourier transform `Φ_L(u) = 2 (1 - cos (L u)) / (L u²)` of `phi L` (the Fejér kernel), with value `L` at `u = 0`. -/
private def Phi (L u : ℝ) : ℝ := if u = 0 then L else 2 * (1 - Real.cos (L * u)) / (L * u ^ 2)

/-- `phi L` is nonnegative. -/
private theorem phi_nonneg (L t : ℝ) : 0 ≤ phi L t := le_max_left _ _

/-- `phi L t = 0` for `|t| ≥ L`. -/
private theorem phi_eq_zero {L t : ℝ} (hL : 0 < L) (ht : L ≤ |t|) : phi L t = 0 := by
  unfold phi; apply max_eq_left; rw [sub_nonpos, le_div_iff₀ hL]; linarith

/-- `phi L` is at most `1`. -/
private theorem phi_le_one {L : ℝ} (hL : 0 < L) (t : ℝ) : phi L t ≤ 1 := by
  unfold phi; apply max_le zero_le_one
  have : 0 ≤ |t| / L := div_nonneg (abs_nonneg t) hL.le
  linarith

/-- `phi L` is continuous. -/
private theorem continuous_phi (L : ℝ) : Continuous (phi L) := by unfold phi; fun_prop

/-- `phi L` has compact support (contained in `[-L, L]`). -/
private theorem hasCompactSupport_phi {L : ℝ} (hL : 0 < L) : HasCompactSupport (phi L) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L))
  intro t ht
  apply phi_eq_zero hL
  rw [mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- `phi L` is integrable. -/
private theorem integrable_phi {L : ℝ} (hL : 0 < L) : Integrable (phi L) :=
  (continuous_phi L).integrable_of_hasCompactSupport (hasCompactSupport_phi hL)

/-- On `[0, L]`, `phi L t = 1 - t / L`. -/
private theorem phi_of_nonneg {L t : ℝ} (hL : 0 < L) (h0 : 0 ≤ t) (h1 : t ≤ L) : phi L t = 1 - t / L := by
  unfold phi; rw [abs_of_nonneg h0]; apply max_eq_right
  rw [sub_nonneg, div_le_one hL]; exact h1

/-- On `[-L, 0]`, `phi L t = 1 + t / L`. -/
private theorem phi_of_nonpos {L t : ℝ} (hL : 0 < L) (h0 : t ≤ 0) (h1 : -L ≤ t) : phi L t = 1 + t / L := by
  unfold phi; rw [abs_of_nonpos h0, neg_div, sub_neg_eq_add]; rw [max_eq_right]
  have : -1 ≤ t / L := by rw [le_div_iff₀ hL]; linarith
  linarith

/-- Derivative of `t ↦ (p + q t) e^{w t}`. -/
private theorem hasDerivAt_aux (p q w : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (p + q * (t : ℂ)) * cexp (w * t))
      ((q + w * (p + q * t)) * cexp (w * t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := hasDerivAt_id t |>.ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => p + q * (t : ℂ)) q t := by
    simpa using (h1.const_mul q).const_add p
  have h3 : HasDerivAt (fun t : ℝ => cexp (w * t)) (cexp (w * t) * w) t := by
    have := (h1.const_mul w).cexp
    simpa using this
  exact (h2.mul h3).congr_deriv (by ring)

/-- `∫₀^L phi L t e^{iut} dt` for `u ≠ 0`. -/
private theorem integral_right_half {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : u ≠ 0) :
    ∫ t in (0:ℝ)..L, (phi L t : ℂ) * cexp (I * u * t) =
      (1 - cexp (I * u * L)) / (L * u ^ 2) + I / u := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  set p : ℂ := -I / u - 1 / (u ^ 2 * L)
  set q : ℂ := I / (u * L)
  have hcongr : ∀ t ∈ Set.uIcc (0:ℝ) L, (phi L t : ℂ) * cexp (I * u * t) =
      (q + (I * u) * (p + q * t)) * cexp ((I * u) * t) := by
    intro t ht
    rw [Set.uIcc_of_le hL.le] at ht
    rw [phi_of_nonneg hL ht.1 ht.2]
    congr 1
    simp only [p, q]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_aux p q (I * u) t)]
  · simp only [p, q]
    push_cast
    simp only [mul_zero, Complex.exp_zero, add_zero, mul_one]
    field_simp
    ring
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- `∫_{-L}^0 phi L t e^{iut} dt` for `u ≠ 0`. -/
private theorem integral_left_half {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : u ≠ 0) :
    ∫ t in (-L)..0, (phi L t : ℂ) * cexp (I * u * t) =
      (1 - cexp (-(I * u * L))) / (L * u ^ 2) - I / u := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  set p : ℂ := -I / u + 1 / (u ^ 2 * L)
  set q : ℂ := -I / (u * L)
  have hcongr : ∀ t ∈ Set.uIcc (-L) 0, (phi L t : ℂ) * cexp (I * u * t) =
      (q + (I * u) * (p + q * t)) * cexp ((I * u) * t) := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    rw [phi_of_nonpos hL ht.2 ht.1]
    congr 1
    simp only [p, q]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_aux p q (I * u) t)]
  · simp only [p, q]
    push_cast
    simp only [mul_zero, Complex.exp_zero, add_zero, mul_one]
    field_simp
    ring_nf
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- `∫₀^L phi L = L / 2`. -/
private theorem integral_right_half_zero {L : ℝ} (hL : 0 < L) :
    ∫ t in (0:ℝ)..L, (phi L t : ℂ) = L / 2 := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hcongr : ∀ t ∈ Set.uIcc (0:ℝ) L, (phi L t : ℂ) = 1 - (t : ℂ) / L := by
    intro t ht
    rw [Set.uIcc_of_le hL.le] at ht
    rw [phi_of_nonneg hL ht.1 ht.2]; push_cast; ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub, intervalIntegral.integral_div,
    intervalIntegral.integral_ofReal (f := fun x => x), integral_id]
  · simp; field_simp; ring
  · exact intervalIntegrable_const
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- `∫_{-L}^0 phi L = L / 2`. -/
private theorem integral_left_half_zero {L : ℝ} (hL : 0 < L) :
    ∫ t in (-L)..0, (phi L t : ℂ) = L / 2 := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hcongr : ∀ t ∈ Set.uIcc (-L) 0, (phi L t : ℂ) = 1 + (t : ℂ) / L := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    rw [phi_of_nonpos hL ht.2 ht.1]; push_cast; ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_add, intervalIntegral.integral_div,
    intervalIntegral.integral_ofReal (f := fun x => x), integral_id]
  · simp; field_simp; ring
  · exact intervalIntegrable_const
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The Fourier transform of the triangle: `∫ phi L t e^{iut} dt = Φ_L(u)`. -/
private theorem fourier_phi {L : ℝ} (hL : 0 < L) (u : ℝ) :
    ∫ t, (phi L t : ℂ) * cexp (I * u * t) = (Phi L u : ℂ) := by
  have hzero : ∀ t ∉ Ioc (-L) L, (phi L t : ℂ) * cexp (I * u * t) = 0 := by
    intro t ht
    rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
    rw [phi_eq_zero hL]
    · simp
    rcases ht with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (Continuous.intervalIntegrable (by have := continuous_phi L; fun_prop) _ _)
      (Continuous.intervalIntegrable (by have := continuous_phi L; fun_prop) _ _)]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  by_cases hu : u = 0
  · subst hu
    simp only [ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [integral_left_half_zero hL, integral_right_half_zero hL, Phi, if_pos rfl]
    ring
  · rw [integral_left_half hL hu, integral_right_half hL hu, Phi, if_neg hu]
    have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
    push_cast
    rw [Complex.cos, show (L : ℂ) * u * I = I * u * L by ring,
      show -((L : ℂ) * u) * I = -(I * u * L) by ring]
    field_simp
    ring

/-- The Fejér kernel is nonnegative. -/
private theorem Phi_nonneg {L : ℝ} (hL : 0 < L) (u : ℝ) : 0 ≤ Phi L u := by
  unfold Phi; split_ifs with hu
  · exact hL.le
  · have := Real.cos_le_one (L * u)
    have : 0 < L * u ^ 2 := by positivity
    positivity

/-- Tail bound `Φ_L(u) ≤ 4 / (L u²)`. -/
private theorem Phi_le_tail {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : u ≠ 0) : Phi L u ≤ 4 / (L * u ^ 2) := by
  unfold Phi; rw [if_neg hu]
  have := Real.neg_one_le_cos (L * u)
  have : 0 < L * u ^ 2 := by positivity
  apply div_le_div_of_nonneg_right _ this.le
  linarith

/-- `Φ_L(u) ≤ L`. -/
private theorem Phi_le_L {L : ℝ} (hL : 0 < L) (u : ℝ) : Phi L u ≤ L := by
  unfold Phi; split_ifs with hu
  · exact le_rfl
  · have h := Real.one_sub_sq_div_two_le_cos (x := L * u)
    have : 0 < L * u ^ 2 := by positivity
    rw [div_le_iff₀ this]
    nlinarith

/-- `Φ_L(u) ≥ L / 2` for `|u| ≤ 1 / L`. -/
private theorem Phi_ge {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : |u| ≤ 1 / L) : L / 2 ≤ Phi L u := by
  unfold Phi; split_ifs with h0
  · linarith
  · have hx : |L * u| ≤ 1 := by
      rw [abs_mul, abs_of_pos hL]; rw [le_div_iff₀ hL] at hu; linarith
    have hb := Real.cos_bound hx
    have h1 : Real.cos (L * u) ≤ 1 - (L * u) ^ 2 / 2 + |L * u| ^ 4 * (5 / 96) := by
      have := (abs_le.mp hb).2; linarith
    have h2 : |L * u| ^ 4 ≤ (L * u) ^ 2 := by
      rw [show |L * u| ^ 4 = (L * u) ^ 2 * |L * u| ^ 2 by rw [← sq_abs (L * u)]; ring]
      have : |L * u| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (L * u)]
      have : 0 ≤ (L * u) ^ 2 := sq_nonneg _
      nlinarith
    have hpos : 0 < L * u ^ 2 := by positivity
    rw [le_div_iff₀ hpos]
    nlinarith

/-- The Fejér kernel is measurable. -/
private theorem measurable_Phi (L : ℝ) : Measurable (Phi L) := by
  unfold Phi
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  fun_prop

/-- `Φ_L(u) ≤ (2 L + 8 / L) / (1 + u²)`. -/
private theorem Phi_le_bound {L : ℝ} (hL : 0 < L) (u : ℝ) : Phi L u ≤ (2 * L + 8 / L) * (1 + u ^ 2)⁻¹ := by
  have h1 : 0 < 1 + u ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h1]
  rcases le_or_gt (|u|) 1 with hu | hu
  · have := Phi_le_L hL u
    have := Phi_nonneg hL u
    have : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
    have : 0 < 8 / L := by positivity
    nlinarith
  · have hu0 : u ≠ 0 := by intro h; rw [h] at hu; norm_num at hu
    have h2 := Phi_le_tail hL hu0
    have hu2 : 1 < u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
    have : 4 / (L * u ^ 2) * (1 + u ^ 2) ≤ 8 / L := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hL]
      nlinarith
    have := Phi_nonneg hL u
    nlinarith

/-- The Fejér kernel is integrable. -/
private theorem integrable_Phi {L : ℝ} (hL : 0 < L) : Integrable (Phi L) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * L + 8 / L))
    (measurable_Phi L).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Phi_nonneg hL u)]
  exact Phi_le_bound hL u

/-- `∫ du / (δ² + u²) = π / δ`. -/
private theorem integral_inv_sq_add_sq {δ : ℝ} (hδ : 0 < δ) : ∫ u : ℝ, (δ ^ 2 + u ^ 2)⁻¹ = Real.pi / δ := by
  have h1 : ∀ u : ℝ, (δ ^ 2 + u ^ 2)⁻¹ = δ⁻¹ ^ 2 * (1 + (u / δ) ^ 2)⁻¹ := by
    intro u; field_simp
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_div (fun w => (1 + w ^ 2)⁻¹) δ,
    integral_univ_inv_one_add_sq, abs_of_pos hδ, smul_eq_mul]
  field_simp

/-- `u ↦ 1 / (δ² + u²)` is integrable. -/
private theorem integrable_inv_sq_add_sq {δ : ℝ} (hδ : 0 < δ) : Integrable (fun u : ℝ => (δ ^ 2 + u ^ 2)⁻¹) := by
  have h1 : (fun u : ℝ => (δ ^ 2 + u ^ 2)⁻¹) = fun u => δ⁻¹ ^ 2 * (1 + (u / δ) ^ 2)⁻¹ := by
    ext u; field_simp
  rw [h1]
  refine Integrable.const_mul ?_ _
  exact (integrable_inv_one_add_sq).comp_div hδ.ne'

/-- tail of the kernel -/
private theorem tail_le {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    ∫ u, Set.indicator {u | δ < |u|} (Phi L) u ≤ 8 * Real.pi / (L * δ) := by
  have hb : ∀ u, Set.indicator {u | δ < |u|} (Phi L) u ≤ (8 / L) * (δ ^ 2 + u ^ 2)⁻¹ := by
    intro u
    by_cases hu : δ < |u|
    · rw [Set.indicator_of_mem (by exact hu)]
      have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu; linarith
      refine (Phi_le_tail hL hu0).trans ?_
      have hu2 : δ ^ 2 < u ^ 2 := by
        rw [← sq_abs u]; exact pow_lt_pow_left₀ hu hδ.le (by norm_num)
      have hu2' : 0 < u ^ 2 := by positivity
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 8 / L * (L * u ^ 2) = 8 * u ^ 2 := by field_simp
      rw [this]; linarith
    · rw [Set.indicator_of_notMem (by exact hu)]
      positivity
  calc ∫ u, Set.indicator {u | δ < |u|} (Phi L) u
      ≤ ∫ u, (8 / L) * (δ ^ 2 + u ^ 2)⁻¹ := by
        apply integral_mono_of_nonneg
        · exact Eventually.of_forall fun u => Set.indicator_nonneg (fun u _ => Phi_nonneg hL u) u
        · exact (integrable_inv_sq_add_sq hδ).const_mul _
        · exact Eventually.of_forall hb
    _ = 8 * Real.pi / (L * δ) := by
        rw [integral_const_mul, integral_inv_sq_add_sq hδ]; field_simp

/-- The total mass of the Fejér kernel is at least `1`. -/
private theorem one_le_integral_Phi {L : ℝ} (hL : 0 < L) : 1 ≤ ∫ u, Phi L u := by
  have hb : ∀ u, Set.indicator (Icc (-(1 / L)) (1 / L)) (fun _ => L / 2) u ≤ Phi L u := by
    intro u
    by_cases hu : u ∈ Icc (-(1 / L)) (1 / L)
    · rw [Set.indicator_of_mem hu]; exact Phi_ge hL (abs_le.mpr hu)
    · rw [Set.indicator_of_notMem hu]; exact Phi_nonneg hL u
  calc (1 : ℝ) = ∫ u, Set.indicator (Icc (-(1 / L)) (1 / L)) (fun _ => L / 2) u := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc]
        rw [smul_eq_mul, max_eq_left (by have : 0 < 1 / L := by positivity
                                         linarith)]
        field_simp; ring
    _ ≤ ∫ u, Phi L u := by
        apply integral_mono_of_nonneg
        · exact Eventually.of_forall fun u => Set.indicator_nonneg (fun u _ => by positivity) u
        · exact integrable_Phi hL
        · exact Eventually.of_forall hb

section Tauberian

variable (a : ℕ → ℝ)

/-- partial sums -/
private def Asum (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n

/-- normalized partial sums in logarithmic variable -/
private def Bf (v : ℝ) : ℝ := Asum a (Real.exp v) * Real.exp (-v)

variable {a}

/-- The partial sums of a nonnegative sequence are monotone. -/
private theorem Asum_mono (ha : ∀ n, 0 ≤ a n) : Monotone (Asum a) := by
  intro x y hxy
  unfold Asum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hxy)
  · intro i _ _; exact ha i

/-- The partial sums of a nonnegative sequence are nonnegative. -/
private theorem Asum_nonneg (ha : ∀ n, 0 ≤ a n) (x : ℝ) : 0 ≤ Asum a x :=
  Finset.sum_nonneg fun i _ => ha i

/-- Linear bound on the partial sums. -/
private theorem Asum_le {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N)
    {x : ℝ} (hx : 0 ≤ x) : Asum a x ≤ M * x :=
  (hM _).trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx) hM0)

/-- `B` is nonnegative. -/
private theorem Bf_nonneg (ha : ∀ n, 0 ≤ a n) (v : ℝ) : 0 ≤ Bf a v :=
  mul_nonneg (Asum_nonneg ha _) (Real.exp_pos _).le

/-- `B` is bounded by `M`. -/
private theorem Bf_le {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N)
    (v : ℝ) : Bf a v ≤ M := by
  unfold Bf
  calc Asum a (Real.exp v) * Real.exp (-v) ≤ (M * Real.exp v) * Real.exp (-v) :=
        mul_le_mul_of_nonneg_right (Asum_le hM0 hM (Real.exp_pos v).le) (Real.exp_pos _).le
    _ = M := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- Monotonicity of `A` gives `B(v) ≥ B(y) e^{-2δ}` for `v ∈ [y, y + 2δ]`. -/
private theorem Bf_ge_of_ge (ha : ∀ n, 0 ≤ a n) {y v δ : ℝ} (h1 : y ≤ v) (h2 : v ≤ y + 2 * δ) :
    Bf a y * Real.exp (-(2 * δ)) ≤ Bf a v := by
  unfold Bf
  rw [mul_assoc, ← Real.exp_add]
  have hA : Asum a (Real.exp y) ≤ Asum a (Real.exp v) :=
    Asum_mono ha (Real.exp_le_exp.mpr h1)
  have hE : Real.exp (-y + -(2 * δ)) ≤ Real.exp (-v) := Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul hA hE (Real.exp_pos _).le (Asum_nonneg ha _)

/-- Monotonicity of `A` gives `B(v) ≤ B(y) e^{2δ}` for `v ∈ [y - 2δ, y]`. -/
private theorem Bf_le_of_le (ha : ∀ n, 0 ≤ a n) {y v δ : ℝ} (h1 : y - 2 * δ ≤ v) (h2 : v ≤ y) :
    Bf a v ≤ Bf a y * Real.exp (2 * δ) := by
  unfold Bf
  rw [mul_assoc, ← Real.exp_add]
  have hA : Asum a (Real.exp v) ≤ Asum a (Real.exp y) :=
    Asum_mono ha (Real.exp_le_exp.mpr h2)
  have hE : Real.exp (-v) ≤ Real.exp (-y + 2 * δ) := Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul hA hE (Real.exp_pos _).le (Asum_nonneg ha _)

/-- The partial sum function is measurable. -/
private theorem measurable_Asum : Measurable (Asum a) := by
  unfold Asum
  exact (measurable_from_nat (f := fun N => ∑ n ∈ Finset.Icc 1 N, a n)).comp Nat.measurable_floor

/-- `B` is measurable. -/
private theorem measurable_Bf : Measurable (Bf a) := by
  unfold Bf
  exact (measurable_Asum.comp Real.measurable_exp).mul (by fun_prop)

/-- `v ↦ B(v) e^{-wv}` is integrable on `(0, ∞)` for `re w > 0`. -/
private theorem integrableOn_Bf_exp {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun v : ℝ => (Bf a v : ℂ) * cexp (-w * v)) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hw).const_mul M) ?_ ?_
  · exact ((measurable_Bf.complex_ofReal).mul (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Bf_nonneg ha v)]
    have : (-w * (v : ℂ)).re = -w.re * v := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (Bf_le hM0 hM v) (Real.exp_pos _).le

/-- Laplace transform representation -/
private theorem laplace_repr {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) (c : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (a n : ℂ)) s / s - c / (s - 1) =
      ∫ v in Ioi 0, ((Bf a v : ℂ) - c) * cexp (-(s - 1) * v) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  have hw : 0 < (s - 1).re := by simp; linarith
  have hO : (fun n ↦ ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound M (Eventually.of_forall fun n => ?_)
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => ha i),
      abs_of_nonneg (Nat.cast_nonneg n)]
    exact hM n
  have h1 := LSeries_eq_mul_integral_of_nonneg a zero_le_one (by simpa using hs) hO ha
  rw [h1, mul_div_cancel_left₀ _ hs0]
  have hcv := integral_comp_exp_Ioi (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (a k : ℂ)) *
      (t : ℂ) ^ (-(s + 1))) 0
  rw [Real.exp_zero] at hcv
  rw [← hcv]
  have h2 : ∀ v : ℝ, Real.exp v • ((∑ k ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, (a k : ℂ)) *
      ((Real.exp v : ℝ) : ℂ) ^ (-(s + 1))) = (Bf a v : ℂ) * cexp (-(s - 1) * v) := by
    intro v
    rw [Complex.real_smul, cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos v).ne'),
      ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]
    unfold Bf Asum
    push_cast
    have he : cexp ↑v * cexp (↑v * -(s + 1)) = cexp (-↑v) * cexp (-(s - 1) * ↑v) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    linear_combination (∑ k ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, (a k : ℂ)) * he
  simp_rw [h2]
  have h3 : (c : ℂ) / (s - 1) = ∫ v in Ioi (0:ℝ), (c : ℂ) * cexp (-(s - 1) * v) := by
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simpa using hw) 0]
    simp only [ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
  rw [h3, ← integral_sub (integrableOn_Bf_exp hM0 ha hM hw)
    ((integrableOn_exp_mul_complex_Ioi (by simpa using hw) 0).const_mul _)]
  congr 1; ext v; ring

/-- For `ε > 0`: `∫ phi(t) G(1 + ε + it) e^{iyt} dt = ∫_{v > 0} (B(v) - c) e^{-εv} Φ(y - v) dv` (Fubini). -/
private theorem fubini_identity {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) (c : ℝ) (G : ℂ → ℂ)
    (hG : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (a n : ℂ)) s / s - c / (s - 1) = G s)
    {L : ℝ} (hL : 0 < L) (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ t, (phi L t : ℂ) * G (1 + ε + t * I) * cexp (I * y * t) =
      ∫ v in Ioi 0, ((Bf a v : ℂ) - c) * cexp (-ε * v) * (Phi L (y - v) : ℂ) := by
  set F : ℝ → ℝ → ℂ := fun t v => (phi L t : ℂ) * (((Bf a v : ℂ) - c) *
    cexp (-(ε + t * I) * v)) * cexp (I * y * t) with hF
  have hL1 : ∀ t : ℝ, (phi L t : ℂ) * G (1 + ε + t * I) * cexp (I * y * t) =
      ∫ v in Ioi 0, F t v := by
    intro t
    have hs : 1 < (1 + ε + t * I : ℂ).re := by simp; linarith
    rw [← hG _ hs, laplace_repr hM0 ha hM c hs, hF]
    simp only
    rw [← integral_const_mul, ← integral_mul_const]
    congr 1; ext v; ring_nf
  have hR1 : ∀ v : ℝ, ∫ t, F t v = ((Bf a v : ℂ) - c) * cexp (-ε * v) * (Phi L (y - v) : ℂ) := by
    intro v
    rw [← fourier_phi hL (y - v), ← integral_const_mul]
    congr 1; ext t
    rw [hF]; simp only
    have : cexp (-(ε + t * I) * v) * cexp (I * y * t) = cexp (-ε * v) * cexp (I * ↑(y - v) * t) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; push_cast; ring_nf
    linear_combination ((phi L t : ℂ) * ((Bf a v : ℂ) - c)) * this
  simp_rw [hL1]
  have hint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    have hprod : Integrable (fun z : ℝ × ℝ => phi L z.1 * ((M + |c|) * Real.exp (-ε * z.2)))
        (volume.prod (volume.restrict (Ioi 0))) :=
      (integrable_phi hL).mul_prod ((exp_neg_integrableOn_Ioi 0 hε).const_mul (M + |c|))
    refine hprod.mono' ?_ (Eventually.of_forall fun z => ?_)
    · have hB := (measurable_Bf (a := a))
      have : Measurable (Function.uncurry F) := by
        rw [hF]
        unfold Function.uncurry
        have := continuous_phi L
        fun_prop
      exact this.aestronglyMeasurable
    · obtain ⟨t, v⟩ := z
      simp only [Function.uncurry, hF]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (phi_nonneg L t), Complex.norm_exp, Complex.norm_exp]
      have h1 : (-(↑ε + ↑t * I) * (v : ℂ)).re = -ε * v := by simp
      have h2 : (I * ↑y * (t : ℂ)).re = 0 := by simp
      rw [h1, h2, Real.exp_zero, mul_one]
      have h3 : ‖(Bf a v : ℂ) - c‖ ≤ M + |c| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (Bf_nonneg ha v)]
        linarith [Bf_le hM0 hM v]
      apply mul_le_mul_of_nonneg_left _ (phi_nonneg L t)
      exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  rw [integral_integral_swap hint]
  simp_rw [hR1]

/-- Letting `ε → 0`: `∫ phi(t) G(1 + it) e^{iyt} dt = ∫_{v > 0} (B(v) - c) Φ(y - v) dv`. -/
private theorem limit_identity {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) (c : ℝ) (G : ℂ → ℂ)
    (hGc : ContinuousOn G {s | 1 ≤ s.re})
    (hG : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (a n : ℂ)) s / s - c / (s - 1) = G s)
    {L : ℝ} (hL : 0 < L) (y : ℝ) :
    ∫ t, (phi L t : ℂ) * G (1 + t * I) * cexp (I * y * t) =
      ∫ v in Ioi 0, ((Bf a v : ℂ) - c) * (Phi L (y - v) : ℂ) := by
  -- the path
  have hpath : ∀ (ε : ℝ), 0 ≤ ε → Continuous (fun t : ℝ => G (1 + ε + t * I)) := by
    intro ε hε
    refine hGc.comp_continuous (by fun_prop) (fun t => ?_)
    simp only [Set.mem_ofPred_eq, add_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]
    linarith
  -- left limit
  have hK : IsCompact ((Icc (1:ℝ) 2) ×ℂ (Icc (-L) L)) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hGc.mono (fun s hs => by
    simp only [mem_reProdIm, mem_Icc] at hs; exact hs.1.1))
  have hLlim : Tendsto (fun ε : ℝ => ∫ t, (phi L t : ℂ) * G (1 + ε + t * I) * cexp (I * y * t))
      (𝓝[>] 0) (𝓝 (∫ t, (phi L t : ℂ) * G (1 + t * I) * cexp (I * y * t))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => C * phi L t) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have h1 := hpath ε (le_of_lt hε)
      have h2 : Continuous fun t : ℝ => (phi L t : ℂ) := by have := continuous_phi L; fun_prop
      have h3 : Continuous fun t : ℝ => cexp (I * y * t) := by fun_prop
      exact ((h2.mul h1).mul h3).aestronglyMeasurable
    · have h1 : Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [h1] with ε hε
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (phi_nonneg L t)]
      have he : ‖cexp (I * y * t)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [he, mul_one]
      by_cases ht : L ≤ |t|
      · rw [phi_eq_zero hL ht]; simp
      · rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ (phi_nonneg L t)
        apply hC
        rw [not_le, abs_lt] at ht
        simp only [mem_reProdIm, mem_Icc, add_re, one_re, ofReal_re, mul_re, I_re, mul_zero,
          ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, one_im, zero_add, mul_im]
        exact ⟨⟨by linarith [hε.1], by linarith [hε.2]⟩, ht.1.le, ht.2.le⟩
    · exact (integrable_phi hL).const_mul C
    · refine Eventually.of_forall fun t => ?_
      have hmem : (1 + t * I : ℂ) ∈ {s : ℂ | 1 ≤ s.re} := by simp
      have hcw := (hGc _ hmem).tendsto
      have hpth : Tendsto (fun ε : ℝ => (1 + ε + t * I : ℂ)) (𝓝[>] 0) (𝓝[{s | 1 ≤ s.re}] (1 + t * I)) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have : Tendsto (fun ε : ℝ => (1 + ε + t * I : ℂ)) (𝓝 0) (𝓝 (1 + (0:ℝ) + t * I)) :=
            (by fun_prop : Continuous fun ε : ℝ => (1 + ε + t * I : ℂ)).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          simp only [add_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
            I_im, mul_one, sub_self, add_zero]
          linarith [mem_Ioi.mp hε]
      exact ((hcw.comp hpth).const_mul _).mul_const _
  -- right limit
  have hRlim : Tendsto (fun ε : ℝ => ∫ v in Ioi 0, ((Bf a v : ℂ) - c) * cexp (-ε * v) *
      (Phi L (y - v) : ℂ)) (𝓝[>] 0) (𝓝 (∫ v in Ioi 0, ((Bf a v : ℂ) - c) * (Phi L (y - v) : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun v => (M + |c|) * Phi L (y - v))
      ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun ε => ?_
      have hB := (measurable_Bf (a := a))
      have hP := measurable_Phi L
      exact (by fun_prop : Measurable fun v : ℝ => ((Bf a v : ℂ) - c) * cexp (-ε * v) *
        (Phi L (y - v) : ℂ)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Phi_nonneg hL _), Complex.norm_exp]
      have h1 : (-(ε : ℂ) * v).re = -ε * v := by simp
      rw [h1]
      have h2 : Real.exp (-ε * v) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := mem_Ioi.mp hε; have := mem_Ioi.mp hv; nlinarith
      have h3 : ‖(Bf a v : ℂ) - c‖ ≤ M + |c| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (Bf_nonneg ha v)]
        linarith [Bf_le hM0 hM v]
      have h4 : 0 ≤ ‖(Bf a v : ℂ) - c‖ := norm_nonneg _
      apply mul_le_mul_of_nonneg_right _ (Phi_nonneg hL _)
      calc ‖(Bf a v : ℂ) - c‖ * Real.exp (-ε * v) ≤ ‖(Bf a v : ℂ) - c‖ * 1 :=
            mul_le_mul_of_nonneg_left h2 h4
        _ ≤ M + |c| := by rw [mul_one]; exact h3
    · exact ((integrable_Phi hL).comp_sub_left y).integrableOn.const_mul _
    · refine Eventually.of_forall fun v => ?_
      have : Tendsto (fun ε : ℝ => cexp (-ε * v)) (𝓝[>] 0) (𝓝 (cexp (-(0:ℝ) * v))) :=
        ((by fun_prop : Continuous fun ε : ℝ => cexp (-ε * v)).tendsto 0).mono_left
          nhdsWithin_le_nhds
      simp only [ofReal_zero, neg_zero, zero_mul, Complex.exp_zero] at this
      simpa using (this.const_mul ((Bf a v : ℂ) - c)).mul_const (Phi L (y - v) : ℂ)
  have heq : (fun ε : ℝ => ∫ t, (phi L t : ℂ) * G (1 + ε + t * I) * cexp (I * y * t)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ∫ v in Ioi 0, ((Bf a v : ℂ) - c) * cexp (-ε * v) * (Phi L (y - v) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact fubini_identity hM0 ha hM c G hG hL y hε
  exact tendsto_nhds_unique (hLlim.congr' heq) hRlim

/-- By the Riemann–Lebesgue lemma, `∫_{v > 0} (B(v) - c) Φ(y - v) dv → 0` as `y → ∞`. -/
private theorem J_tendsto {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) (c : ℝ) (G : ℂ → ℂ)
    (hGc : ContinuousOn G {s | 1 ≤ s.re})
    (hG : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (a n : ℂ)) s / s - c / (s - 1) = G s)
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun y : ℝ => ∫ v in Ioi 0, (Bf a v - c) * Phi L (y - v)) atTop (𝓝 0) := by
  have hRL := Real.tendsto_integral_exp_smul_cocompact (fun t : ℝ => (phi L t : ℂ) * G (1 + t * I))
  have hw : Tendsto (fun y : ℝ => -y / (2 * Real.pi)) atTop (cocompact ℝ) := by
    refine Tendsto.mono_right ?_ atBot_le_cocompact
    have : Tendsto (fun y : ℝ => -y) atTop atBot := tendsto_neg_atTop_atBot
    exact this.atBot_div_const (by positivity)
  have hC := hRL.comp hw
  have heq : ∀ y : ℝ, ((fun w : ℝ => ∫ v : ℝ, Real.fourierChar (-(v * w)) •
      ((fun t : ℝ => (phi L t : ℂ) * G (1 + t * I)) v)) ∘ (fun y : ℝ => -y / (2 * Real.pi))) y =
      ((∫ v in Ioi 0, (Bf a v - c) * Phi L (y - v) : ℝ) : ℂ) := by
    intro y
    simp only [Function.comp]
    rw [← integral_complex_ofReal]
    push_cast
    rw [← limit_identity hM0 ha hM c G hGc hG hL y]
    congr 1; ext t
    rw [Circle.smul_def, Real.fourierChar_apply]
    simp only [smul_eq_mul]
    have : (↑(2 * Real.pi * -(t * (-y / (2 * Real.pi)))) * I : ℂ) = I * y * t := by
      push_cast
      field_simp
    rw [this]; ring
  have hC' : Tendsto (fun y : ℝ => ((∫ v in Ioi 0, (Bf a v - c) * Phi L (y - v) : ℝ) : ℂ))
      atTop (𝓝 0) := by
    refine hC.congr (fun y => heq y)
  have := (Complex.continuous_re.tendsto 0).comp hC'
  refine this.congr (fun y => ?_)
  simp only [Function.comp, Complex.ofReal_re]

/-- Translates of the Fejér kernel are integrable. -/
private theorem integrable_Phi_sub {L : ℝ} (hL : 0 < L) (y : ℝ) : Integrable (fun v => Phi L (y - v)) :=
  (integrable_Phi hL).comp_sub_left y

/-- `v ↦ B(v) Φ(y - v)` is integrable on every set. -/
private theorem integrableOn_Bf_Phi {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (s : Set ℝ) : IntegrableOn (fun v => Bf a v * Phi L (y - v)) s := by
  refine Integrable.mono' ((integrable_Phi_sub hL y).integrableOn.const_mul M) ?_ ?_
  · have := measurable_Bf (a := a); have := measurable_Phi L
    exact (by fun_prop : Measurable fun v => Bf a v * Phi L (y - v)).aestronglyMeasurable
  · refine Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Bf_nonneg ha v) (Phi_nonneg hL _))]
    exact mul_le_mul_of_nonneg_right (Bf_le hM0 hM v) (Phi_nonneg hL _)

/-- `∫_{v > 0} Φ(y - v) dv → ∫ Φ` as `y → ∞`. -/
private theorem tail_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (fun y : ℝ => ∫ v in Ioi 0, Phi L (y - v)) atTop (𝓝 (∫ u, Phi L u)) := by
  have hsplit : ∀ y, ∫ v in Ioi 0, Phi L (y - v) = (∫ u, Phi L u) - ∫ v in Iic 0, Phi L (y - v) := by
    intro y
    have := integral_add_compl (measurableSet_Ioi (a := (0:ℝ))) (integrable_Phi_sub hL y)
    have h2 : ∫ v, Phi L (y - v) = ∫ u, Phi L u :=
      integral_sub_left_eq_self (fun u => Phi L u) volume y
    rw [compl_Ioi, h2] at this
    linarith
  simp_rw [hsplit]
  have hE : Tendsto (fun y : ℝ => ∫ v in Iic 0, Phi L (y - v)) atTop (𝓝 0) := by
    have hub : Tendsto (fun y : ℝ => 16 * Real.pi / L * y⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (16 * Real.pi / L)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
    · exact Eventually.of_forall fun y => setIntegral_nonneg measurableSet_Iic
        (fun v _ => Phi_nonneg hL _)
    · filter_upwards [eventually_gt_atTop 0] with y hy
      rw [← integral_indicator measurableSet_Iic]
      calc ∫ v, Set.indicator (Iic 0) (fun v => Phi L (y - v)) v
          ≤ ∫ v, Set.indicator {u | y / 2 < |u|} (Phi L) (y - v) := by
            apply integral_mono_of_nonneg
            · exact Eventually.of_forall fun v =>
                Set.indicator_nonneg (fun v _ => Phi_nonneg hL _) v
            · have : Integrable (Set.indicator {u | y / 2 < |u|} (Phi L)) :=
                (integrable_Phi hL).indicator (measurableSet_lt measurable_const measurable_abs)
              exact this.comp_sub_left y
            · refine Eventually.of_forall fun v => ?_
              by_cases hv : v ∈ Iic 0
              · simp only [mem_Iic] at hv
                have hmem : y - v ∈ {u : ℝ | y / 2 < |u|} := by
                  show y / 2 < |y - v|
                  rw [abs_of_pos (by linarith)]; linarith
                rw [Set.indicator_of_mem (show v ∈ Iic 0 from hv)]
                dsimp only
                rw [Set.indicator_of_mem hmem]
              · rw [Set.indicator_of_notMem hv]
                exact Set.indicator_nonneg (fun u _ => Phi_nonneg hL u) _
        _ = ∫ u, Set.indicator {u | y / 2 < |u|} (Phi L) u :=
            integral_sub_left_eq_self (Set.indicator {u | y / 2 < |u|} (Phi L)) volume y
        _ ≤ 8 * Real.pi / (L * (y / 2)) := tail_le hL (by linarith)
        _ = 16 * Real.pi / L * y⁻¹ := by field_simp; ring
  simpa using (tendsto_const_nhds (x := ∫ u, Phi L u)).sub hE

/-- `∫_{v > 0} B(v) Φ(y - v) dv → c ∫ Φ` as `y → ∞`. -/
private theorem I_tendsto {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) (c : ℝ) (G : ℂ → ℂ)
    (hGc : ContinuousOn G {s | 1 ≤ s.re})
    (hG : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (a n : ℂ)) s / s - c / (s - 1) = G s)
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun y : ℝ => ∫ v in Ioi 0, Bf a v * Phi L (y - v)) atTop
      (𝓝 (c * ∫ u, Phi L u)) := by
  have hsplit : ∀ y : ℝ, ∫ v in Ioi 0, Bf a v * Phi L (y - v) =
      (∫ v in Ioi 0, (Bf a v - c) * Phi L (y - v)) + c * ∫ v in Ioi 0, Phi L (y - v) := by
    intro y
    rw [← integral_const_mul, ← integral_add]
    · congr 1; ext v; ring
    · simp_rw [sub_mul]
      exact (integrableOn_Bf_Phi hM0 ha hM hL y _).sub
        ((integrable_Phi_sub hL y).integrableOn.const_mul c)
    · exact (integrable_Phi_sub hL y).integrableOn.const_mul c
  simp_rw [hsplit]
  simpa using (J_tendsto hM0 ha hM c G hGc hG hL).add ((tail_tendsto hL).const_mul c)

/-- `{u | δ < |u|}` is measurable. -/
private theorem measurableSet_far (δ : ℝ) : MeasurableSet {u : ℝ | δ < |u|} :=
  measurableSet_lt measurable_const measurable_abs

/-- `{u | |u| ≤ δ}` is measurable. -/
private theorem measurableSet_near (δ : ℝ) : MeasurableSet {u : ℝ | |u| ≤ δ} :=
  measurableSet_le measurable_abs measurable_const

/-- Mass of the kernel near `0` equals total mass minus the tail. -/
private theorem near_eq {L : ℝ} (hL : 0 < L) (δ : ℝ) :
    ∫ u, Set.indicator {u | |u| ≤ δ} (Phi L) u =
      (∫ u, Phi L u) - ∫ u, Set.indicator {u | δ < |u|} (Phi L) u := by
  rw [eq_sub_iff_add_eq, ← integral_add ((integrable_Phi hL).indicator (measurableSet_near δ))
    ((integrable_Phi hL).indicator (measurableSet_far δ))]
  congr 1; ext u
  by_cases hu : |u| ≤ δ
  · rw [Set.indicator_of_mem (show u ∈ {u : ℝ | |u| ≤ δ} from hu),
      Set.indicator_of_notMem (show u ∉ {u : ℝ | δ < |u|} from not_lt.mpr hu), add_zero]
  · rw [Set.indicator_of_notMem (show u ∉ {u : ℝ | |u| ≤ δ} from hu),
      Set.indicator_of_mem (show u ∈ {u : ℝ | δ < |u|} from not_le.mp hu), zero_add]

/-- Tauberian upper estimate: `B(y) e^{-2δ} (∫ Φ - tail) ≤ ∫_{v > 0} B(v) Φ(y + δ - v) dv`. -/
private theorem upper_bound {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) {L : ℝ} (hL : 0 < L) {y δ : ℝ}
    (hy : 0 < y) :
    Bf a y * Real.exp (-(2 * δ)) * ((∫ u, Phi L u) - ∫ u, Set.indicator {u | δ < |u|} (Phi L) u)
      ≤ ∫ v in Ioi 0, Bf a v * Phi L (y + δ - v) := by
  rw [← near_eq hL δ, ← integral_sub_left_eq_self _ volume (y + δ), ← integral_const_mul,
    ← integral_indicator measurableSet_Ioi]
  apply integral_mono
  · exact (((integrable_Phi hL).indicator (measurableSet_near δ)).comp_sub_left (y + δ)).const_mul _
  · exact (integrableOn_Bf_Phi hM0 ha hM hL (y + δ) (Ioi 0)).integrable_indicator measurableSet_Ioi
  · intro v
    dsimp only
    have hc : 0 ≤ Bf a y * Real.exp (-(2 * δ)) :=
      mul_nonneg (Bf_nonneg ha y) (Real.exp_pos _).le
    by_cases hv : |y + δ - v| ≤ δ
    · rw [Set.indicator_of_mem (show y + δ - v ∈ {u : ℝ | |u| ≤ δ} from hv)]
      rw [abs_le] at hv
      have hv0 : v ∈ Ioi 0 := by simp only [mem_Ioi]; linarith
      rw [Set.indicator_of_mem hv0]
      exact mul_le_mul_of_nonneg_right (Bf_ge_of_ge ha (by linarith) (by linarith))
        (Phi_nonneg hL _)
    · rw [Set.indicator_of_notMem (show y + δ - v ∉ {u : ℝ | |u| ≤ δ} from hv), mul_zero]
      exact Set.indicator_nonneg (fun v _ => mul_nonneg (Bf_nonneg ha v) (Phi_nonneg hL _)) v

/-- Tauberian lower estimate: `∫_{v > 0} B(v) Φ(y - δ - v) dv ≤ B(y) e^{2δ} ∫ Φ + M · tail`. -/
private theorem lower_bound {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) {L : ℝ} (hL : 0 < L) (y δ : ℝ) :
    ∫ v in Ioi 0, Bf a v * Phi L (y - δ - v) ≤
      Bf a y * Real.exp (2 * δ) * (∫ u, Phi L u) +
        M * ∫ u, Set.indicator {u | δ < |u|} (Phi L) u := by
  rw [← integral_sub_left_eq_self (Phi L) volume (y - δ),
    ← integral_sub_left_eq_self (Set.indicator {u | δ < |u|} (Phi L)) volume (y - δ),
    ← integral_const_mul, ← integral_const_mul, ← integral_add,
    ← integral_indicator measurableSet_Ioi]
  · apply integral_mono
    · exact (integrableOn_Bf_Phi hM0 ha hM hL (y - δ) (Ioi 0)).integrable_indicator measurableSet_Ioi
    · exact ((integrable_Phi_sub hL (y - δ)).const_mul _).add
        ((((integrable_Phi hL).indicator (measurableSet_far δ)).comp_sub_left (y - δ)).const_mul _)
    · intro v
      dsimp only
      have hfar : 0 ≤ M * Set.indicator {u | δ < |u|} (Phi L) (y - δ - v) :=
        mul_nonneg hM0 (Set.indicator_nonneg (fun u _ => Phi_nonneg hL u) _)
      have hnear : 0 ≤ Bf a y * Real.exp (2 * δ) * Phi L (y - δ - v) :=
        mul_nonneg (mul_nonneg (Bf_nonneg ha y) (Real.exp_pos _).le) (Phi_nonneg hL _)
      by_cases hv0 : v ∈ Ioi 0
      · rw [Set.indicator_of_mem hv0]
        by_cases hv : |y - δ - v| ≤ δ
        · rw [abs_le] at hv
          have := mul_le_mul_of_nonneg_right (Bf_le_of_le ha (y := y) (v := v) (δ := δ)
            (by linarith) (by linarith)) (Phi_nonneg hL (y - δ - v))
          linarith
        · rw [Set.indicator_of_mem (show y - δ - v ∈ {u : ℝ | δ < |u|} from not_le.mp hv)]
          have := mul_le_mul_of_nonneg_right (Bf_le hM0 hM v) (Phi_nonneg hL (y - δ - v))
          linarith
      · rw [Set.indicator_of_notMem hv0]
        linarith
  · exact (integrable_Phi_sub hL (y - δ)).const_mul _
  · exact (((integrable_Phi hL).indicator (measurableSet_far δ)).comp_sub_left (y - δ)).const_mul _

/-- The tail of the kernel is nonnegative. -/
private theorem tail_nonneg {L : ℝ} (hL : 0 < L) (δ : ℝ) :
    0 ≤ ∫ u, Set.indicator {u | δ < |u|} (Phi L) u :=
  integral_nonneg fun u => Set.indicator_nonneg (fun u _ => Phi_nonneg hL u) u

/-- `B(y) → c` as `y → ∞`. -/
private theorem tendsto_Bf {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) (c : ℝ) (hc : 0 ≤ c) (G : ℂ → ℂ)
    (hGc : ContinuousOn G {s | 1 ≤ s.re})
    (hG : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (a n : ℂ)) s / s - c / (s - 1) = G s) :
    Tendsto (Bf a) atTop (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro c' hc'
    rcases lt_or_ge c' 0 with h0 | h0
    · exact Eventually.of_forall fun y => h0.trans_le (Bf_nonneg ha y)
    -- choose δ
    have hδlim : Tendsto (fun δ : ℝ => Real.exp (-(2 * δ)) * c) (𝓝[>] 0) (𝓝 c) := by
      have : Tendsto (fun δ : ℝ => Real.exp (-(2 * δ)) * c) (𝓝 0) (𝓝 (Real.exp (-(2 * 0)) * c)) :=
        ((by fun_prop : Continuous fun δ : ℝ => Real.exp (-(2 * δ)) * c).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    obtain ⟨δ, hδc, hδ⟩ := ((hδlim.eventually (lt_mem_nhds hc')).and self_mem_nhdsWithin).exists
    have hδ : 0 < δ := hδ
    -- choose L
    have hLlim : Tendsto (fun L : ℝ => Real.exp (-(2 * δ)) * (c - M * (8 * Real.pi / δ * L⁻¹)))
        atTop (𝓝 (Real.exp (-(2 * δ)) * c)) := by
      have := ((tendsto_inv_atTop_zero.const_mul (8 * Real.pi / δ)).const_mul M).const_sub c
      simpa using this.const_mul (Real.exp (-(2 * δ)))
    obtain ⟨L, hLc, hL⟩ := ((hLlim.eventually (lt_mem_nhds hδc)).and
      (eventually_gt_atTop 0)).exists
    set K := ∫ u, Phi L u with hK
    set τ := ∫ u, Set.indicator {u | δ < |u|} (Phi L) u with hτ
    have hK1 : 1 ≤ K := one_le_integral_Phi hL
    have hτ0 : 0 ≤ τ := tail_nonneg hL δ
    have hτ1 : τ ≤ 8 * Real.pi / δ * L⁻¹ := by
      have := tail_le hL hδ; rw [← hτ] at this
      calc τ ≤ 8 * Real.pi / (L * δ) := this
        _ = 8 * Real.pi / δ * L⁻¹ := by field_simp
    have hE : 0 < Real.exp (2 * δ) * K := by positivity
    have hlim : Tendsto (fun y : ℝ => ((∫ v in Ioi 0, Bf a v * Phi L (y - δ - v)) - M * τ) /
        (Real.exp (2 * δ) * K)) atTop (𝓝 ((c * K - M * τ) / (Real.exp (2 * δ) * K))) := by
      have h1 := (I_tendsto hM0 ha hM c G hGc hG hL).comp
        (tendsto_atTop_add_const_right _ (-δ) tendsto_id)
      have h2 : Tendsto (fun y : ℝ => ∫ v in Ioi 0, Bf a v * Phi L (y - δ - v)) atTop
          (𝓝 (c * K)) := by
        refine h1.congr (fun y => ?_)
        simp only [Function.comp, id, ← sub_eq_add_neg]
      exact (h2.sub_const _).div_const _
    have hval : c' < (c * K - M * τ) / (Real.exp (2 * δ) * K) := by
      rw [lt_div_iff₀ hE]
      have e1 : Real.exp (-(2 * δ)) * Real.exp (2 * δ) = 1 := by
        rw [← Real.exp_add]; simp
      have hMτ : M * τ ≤ M * (8 * Real.pi / δ * L⁻¹) := mul_le_mul_of_nonneg_left hτ1 hM0
      have hMτK : M * τ ≤ M * τ * K := le_mul_of_one_le_right (mul_nonneg hM0 hτ0) hK1
      -- c' * exp(2δ) < c - M*bound ≤ c - M τ
      have h3 : c' * Real.exp (2 * δ) < c - M * (8 * Real.pi / δ * L⁻¹) := by
        have := mul_lt_mul_of_pos_right hLc (Real.exp_pos (2 * δ))
        calc c' * Real.exp (2 * δ) < Real.exp (-(2 * δ)) * (c - M * (8 * Real.pi / δ * L⁻¹)) *
              Real.exp (2 * δ) := this
          _ = c - M * (8 * Real.pi / δ * L⁻¹) := by
            rw [mul_comm, ← mul_assoc, mul_comm (Real.exp (2 * δ)), e1, one_mul]
      have h4 : c' * Real.exp (2 * δ) * K ≤ (c - M * τ) * K := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
      nlinarith
    filter_upwards [hlim.eventually (lt_mem_nhds hval)] with y hy
    refine hy.trans_le ?_
    rw [div_le_iff₀ hE]
    have := lower_bound hM0 ha hM hL y δ
    rw [← hK, ← hτ] at this
    linarith
  · intro c' hc'
    have hδlim : Tendsto (fun δ : ℝ => Real.exp (2 * δ) * c) (𝓝[>] 0) (𝓝 c) := by
      have : Tendsto (fun δ : ℝ => Real.exp (2 * δ) * c) (𝓝 0) (𝓝 (Real.exp (2 * 0) * c)) :=
        ((by fun_prop : Continuous fun δ : ℝ => Real.exp (2 * δ) * c).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    obtain ⟨δ, hδc, hδ⟩ := ((hδlim.eventually (gt_mem_nhds hc')).and self_mem_nhdsWithin).exists
    have hδ : 0 < δ := hδ
    have hLlim : Tendsto (fun L : ℝ => Real.exp (2 * δ) * c / (1 - 8 * Real.pi / δ * L⁻¹))
        atTop (𝓝 (Real.exp (2 * δ) * c)) := by
      have := (tendsto_inv_atTop_zero.const_mul (8 * Real.pi / δ)).const_sub 1
      have h := (tendsto_const_nhds (x := Real.exp (2 * δ) * c)).div this (by simp)
      simp only [mul_zero, sub_zero, div_one] at h
      exact h
    have hsmall : Tendsto (fun L : ℝ => 8 * Real.pi / δ * L⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (8 * Real.pi / δ)
    obtain ⟨L, ⟨hLc, hL1⟩, hL⟩ := (((hLlim.eventually (gt_mem_nhds hδc)).and
      (hsmall.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)))).and
      (eventually_gt_atTop 0)).exists
    set t₀ := 8 * Real.pi / δ * L⁻¹ with ht₀
    set K := ∫ u, Phi L u with hK
    set τ := ∫ u, Set.indicator {u | δ < |u|} (Phi L) u with hτ
    have hK1 : 1 ≤ K := one_le_integral_Phi hL
    have hτ0 : 0 ≤ τ := tail_nonneg hL δ
    have hτ1 : τ ≤ t₀ := by
      have := tail_le hL hδ; rw [← hτ] at this
      calc τ ≤ 8 * Real.pi / (L * δ) := this
        _ = t₀ := by rw [ht₀]; field_simp
    have hKτ : 0 < K - τ := by linarith
    have hlim : Tendsto (fun y : ℝ => (∫ v in Ioi 0, Bf a v * Phi L (y + δ - v)) *
        Real.exp (2 * δ) / (K - τ)) atTop (𝓝 (c * K * Real.exp (2 * δ) / (K - τ))) := by
      have h1 := (I_tendsto hM0 ha hM c G hGc hG hL).comp
        (tendsto_atTop_add_const_right _ δ tendsto_id)
      have h2 : Tendsto (fun y : ℝ => ∫ v in Ioi 0, Bf a v * Phi L (y + δ - v)) atTop
          (𝓝 (c * K)) := by
        refine h1.congr (fun y => ?_)
        simp only [Function.comp, id]
      exact (h2.mul_const _).div_const _
    have hval : c * K * Real.exp (2 * δ) / (K - τ) < c' := by
      rw [div_lt_iff₀ hKτ]
      have ht1 : 0 < 1 - t₀ := by linarith
      rw [div_lt_iff₀ ht1] at hLc
      -- c K e (1 - t0) ≤ e c (K - τ) and e c < c' (1 - t0) ... combine
      have hE := Real.exp_pos (2 * δ)
      have k1 : c * K * Real.exp (2 * δ) * (1 - t₀) ≤ Real.exp (2 * δ) * c * (K - τ) := by
        have : c * τ ≤ c * K * t₀ := by
          have : τ ≤ K * t₀ := hτ1.trans (le_mul_of_one_le_left (by linarith) hK1)
          calc c * τ ≤ c * (K * t₀) := mul_le_mul_of_nonneg_left this hc
            _ = c * K * t₀ := by ring
        nlinarith
      have k2 : Real.exp (2 * δ) * c * (K - τ) < c' * (1 - t₀) * (K - τ) :=
        mul_lt_mul_of_pos_right hLc hKτ
      have k3 : c' * (1 - t₀) * (K - τ) ≤ c' * (K - τ) * (1 - t₀) := le_of_eq (by ring)
      have k4 : c * K * Real.exp (2 * δ) * (1 - t₀) < c' * (K - τ) * (1 - t₀) := by linarith
      exact lt_of_mul_lt_mul_right k4 ht1.le
    filter_upwards [hlim.eventually (gt_mem_nhds hval), eventually_gt_atTop 0] with y hy hy0
    refine lt_of_le_of_lt ?_ hy
    rw [le_div_iff₀ hKτ]
    have := upper_bound hM0 ha hM hL (δ := δ) hy0
    rw [← hK, ← hτ] at this
    have e1 : Real.exp (-(2 * δ)) * Real.exp (2 * δ) = 1 := by
      rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_right this (Real.exp_pos (2 * δ)).le
    calc Bf a y * (K - τ) = Bf a y * Real.exp (-(2 * δ)) * (K - τ) * Real.exp (2 * δ) := by
          linear_combination (-(Bf a y * (K - τ))) * e1
      _ ≤ _ := this

/-- A Wiener–Ikehara type Tauberian theorem for nonnegative coefficients with linearly bounded
partial sums. -/
private theorem tauberian {M : ℝ} (hM0 : 0 ≤ M) (ha : ∀ n, 0 ≤ a n)
    (hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ M * N) (c : ℝ) (hc : 0 ≤ c) (G : ℂ → ℂ)
    (hGc : ContinuousOn G {s | 1 ≤ s.re})
    (hG : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (a n : ℂ)) s / s - c / (s - 1) = G s) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, a n) / N) atTop (𝓝 c) := by
  have h := (tendsto_Bf hM0 ha hM c hc G hGc hG).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp, Bf, Asum]
  rw [Real.exp_log hN', Real.exp_neg, Real.exp_log hN', Nat.floor_natCast, div_eq_mul_inv]

end Tauberian

end

end Tauber

namespace Arith

open ArithmeticFunction
open scoped LSeries.notation

/-- the weight `2^ω(m)` on odd `m` all of whose prime factors are `3 mod 4` -/
private def gN (m : ℕ) : ℕ :=
  if Odd m ∧ (∀ p ∈ m.primeFactors, p % 4 = 3) then 2 ^ m.primeFactors.card else 0

/-- `g 0 = 0`. -/
private theorem gN_zero : gN 0 = 0 := by simp [gN]

/-- `g 1 = 1`. -/
private theorem gN_one : gN 1 = 1 := by simp [gN]

/-- `g` is multiplicative. -/
private theorem gN_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n) :
    gN (m * n) = gN m * gN n := by
  unfold gN
  rw [Nat.primeFactors_mul hm hn, Finset.card_union_of_disjoint h.disjoint_primeFactors]
  simp only [Nat.odd_mul]
  by_cases h1 : Odd m ∧ ∀ p ∈ m.primeFactors, p % 4 = 3
  · by_cases h2 : Odd n ∧ ∀ p ∈ n.primeFactors, p % 4 = 3
    · rw [if_pos h1, if_pos h2, if_pos, pow_add]
      refine ⟨⟨h1.1, h2.1⟩, fun p hp => ?_⟩
      rcases Finset.mem_union.mp hp with hp | hp
      · exact h1.2 p hp
      · exact h2.2 p hp
    · rw [if_neg h2, if_neg, mul_zero]
      rintro ⟨⟨_, ho⟩, hp⟩
      exact h2 ⟨ho, fun p h => hp p (Finset.mem_union_right _ h)⟩
  · rw [if_neg h1, if_neg, zero_mul]
    rintro ⟨⟨ho, _⟩, hp⟩
    exact h1 ⟨ho, fun p h => hp p (Finset.mem_union_left _ h)⟩

/-- Values of `g` at prime powers. -/
private theorem gN_prime_pow {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ≠ 0) :
    gN (p ^ j) = if p % 4 = 3 then 2 else 0 := by
  unfold gN
  rw [Nat.primeFactors_prime_pow hj hp, Finset.card_singleton, pow_one]
  simp only [Finset.mem_singleton, forall_eq]
  by_cases h3 : p % 4 = 3
  · rw [if_pos h3, if_pos]
    refine ⟨Odd.pow ?_, h3⟩
    rw [Nat.odd_iff]; omega
  · rw [if_neg h3, if_neg]
    exact fun h => h3 h.2

/-- `g` as an arithmetic function -/
private def gA : ArithmeticFunction ℤ := ⟨fun m => (gN m : ℤ), by simp [gN_zero]⟩

/-- Values of `gA`. -/
private theorem gA_apply (m : ℕ) : gA m = (gN m : ℤ) := rfl

/-- `gA` is multiplicative. -/
private theorem gA_mult : gA.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨by simp [gA_apply, gN_one], fun {m n} hm hn h => ?_⟩
  simp only [gA_apply, gN_mul hm hn h, Nat.cast_mul]

/-- `χ₄` as an arithmetic function -/
private def χA : ArithmeticFunction ℤ := toArithmeticFunction (fun n : ℕ => ZMod.χ₄ (n : ZMod 4))

/-- Values of `χA`. -/
private theorem χA_apply {n : ℕ} (hn : n ≠ 0) : χA n = ZMod.χ₄ (n : ZMod 4) := by
  simp [χA, toArithmeticFunction, hn]

/-- `χA` is multiplicative. -/
private theorem χA_mult : χA.IsMultiplicative :=
  DirichletCharacter.isMultiplicative_toArithmeticFunction (N := 4) ZMod.χ₄

/-- indicator of odd numbers -/
private def oA : ArithmeticFunction ℤ := ⟨fun n => if Odd n then 1 else 0, by simp⟩

/-- Values of `oA`. -/
private theorem oA_apply (n : ℕ) : oA n = if Odd n then 1 else 0 := rfl

/-- `oA` is multiplicative. -/
private theorem oA_mult : oA.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨by simp [oA_apply], fun {m n} _ _ _ => ?_⟩
  simp only [oA_apply, Nat.odd_mul]
  by_cases h1 : Odd m <;> by_cases h2 : Odd n <;> simp [h1, h2]

/-- Dirichlet convolution at a prime power. -/
private theorem mul_prime_pow (f g : ArithmeticFunction ℤ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (f * g) (p ^ i) = ∑ j ∈ Finset.range (i + 1), f (p ^ j) * g (p ^ (i - j)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => f x * g y), Nat.divisors_prime_pow hp,
    Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hj) hp.pos]

/-- `χ₄` is completely multiplicative on powers. -/
private theorem χ₄_pow (p j : ℕ) : ZMod.χ₄ ((p ^ j : ℕ) : ZMod 4) = ZMod.χ₄ (p : ZMod 4) ^ j := by
  rw [Nat.cast_pow, map_pow]

/-- `(-1)^i + 2 ∑_{1 ≤ j ≤ i} (-1)^{i-j} = 1`. -/
private theorem sum_alt (i : ℕ) :
    ∑ j ∈ Finset.range (i + 1), ((if j = 0 then 1 else 2 : ℤ)) * (-1) ^ (i - j) = 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, if_neg (by omega), mul_one]
    have : ∑ j ∈ Finset.range (i + 1), ((if j = 0 then 1 else 2 : ℤ)) * (-1) ^ (i + 1 - j) =
        -∑ j ∈ Finset.range (i + 1), ((if j = 0 then 1 else 2 : ℤ)) * (-1) ^ (i - j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [show i + 1 - j = (i - j) + 1 by omega, pow_succ]
      ring
    rw [this, ih]; norm_num

/-- The key identity `g * χ₄ = 1_odd`. -/
private theorem gA_mul_χA : gA * χA = oA := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (gA_mult.mul χA_mult) _ oA_mult]
  intro p i hp
  rw [mul_prime_pow _ _ hp]
  rcases Nat.Prime.eq_two_or_odd hp with h2 | hodd
  · -- p = 2
    subst h2
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp [gA_apply, gN_one, χA_apply, oA_apply]
    · rw [oA_apply, if_neg (by rw [Nat.not_odd_iff_even]; exact (Nat.even_pow' hi.ne').mpr even_two)]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        rw [Nat.sub_zero, χA_apply (by positivity), χ₄_pow, ZMod.χ₄_nat_eq_if_mod_four 2]
        simp [hi.ne']
      · rw [gA_apply, gN_prime_pow Nat.prime_two hj0.ne']; simp
  · have hpo : Odd p := Nat.odd_iff.mpr hodd
    rw [oA_apply, if_pos (hpo.pow)]
    have hmod : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hmod with h1 | h3
    · rw [Finset.sum_eq_single 0]
      · rw [pow_zero, gA_apply, gN_one, Nat.sub_zero, χA_apply (pow_pos hp.pos _).ne', χ₄_pow,
          ZMod.χ₄_nat_one_mod_four h1]
        simp
      · intro j _ hj0
        rw [gA_apply, gN_prime_pow hp hj0, if_neg (by omega)]; simp
      · intro h; simp at h
    · have : ∀ j ∈ Finset.range (i + 1), gA (p ^ j) * χA (p ^ (i - j)) =
          ((if j = 0 then 1 else 2 : ℤ)) * (-1) ^ (i - j) := by
        intro j _
        rw [χA_apply (pow_pos hp.pos _).ne', χ₄_pow, ZMod.χ₄_nat_three_mod_four h3, gA_apply]
        by_cases hj0 : j = 0
        · subst hj0; simp [gN_one]
        · rw [gN_prime_pow hp hj0, if_pos h3, if_neg hj0]; simp
      rw [Finset.sum_congr rfl this, sum_alt]

/-- partial sums of `χ₄` -/
private theorem χA_partial (k : ℕ) :
    ∑ m ∈ Finset.Ioc 0 k, χA m = if k % 4 = 1 ∨ k % 4 = 2 then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), ih, χA_apply (by omega),
      ZMod.χ₄_nat_eq_if_mod_four (k + 1)]
    split_ifs <;> omega

/-- Partial sums of `χ₄` are nonnegative. -/
private theorem χA_partial_nonneg (k : ℕ) : 0 ≤ ∑ m ∈ Finset.Ioc 0 k, χA m := by
  rw [χA_partial]; split_ifs <;> norm_num

/-- `∑_{N/2 < n ≤ N} g(n) ≤ N`, from `g * χ₄ = 1_odd`. -/
private theorem window_le (N : ℕ) : ∑ n ∈ Finset.Ioc (N / 2) N, (gN n : ℤ) ≤ N := by
  have key := sum_Ioc_mul_eq_sum_sum gA χA N
  rw [gA_mul_χA] at key
  have hL : ∑ n ∈ Finset.Ioc 0 N, oA n ≤ N := by
    calc ∑ n ∈ Finset.Ioc 0 N, oA n ≤ ∑ n ∈ Finset.Ioc 0 N, (1 : ℤ) := by
          apply Finset.sum_le_sum; intro n _; rw [oA_apply]; split_ifs <;> norm_num
      _ = N := by simp
  have hR : ∑ n ∈ Finset.Ioc (N / 2) N, (gN n : ℤ) ≤
      ∑ n ∈ Finset.Ioc 0 N, gA n * ∑ m ∈ Finset.Ioc 0 (N / n), χA m := by
    calc ∑ n ∈ Finset.Ioc (N / 2) N, (gN n : ℤ)
        = ∑ n ∈ Finset.Ioc (N / 2) N, gA n * ∑ m ∈ Finset.Ioc 0 (N / n), χA m := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_Ioc] at hn
          have hdiv : N / n = 1 := by
            apply Nat.div_eq_of_lt_le
            · omega
            · have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mp hn.1; omega
          rw [hdiv, χA_partial, gA_apply]; norm_num
      _ ≤ ∑ n ∈ Finset.Ioc 0 N, gA n * ∑ m ∈ Finset.Ioc 0 (N / n), χA m := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Ioc_subset_Ioc (Nat.zero_le _) le_rfl
          · intro n _ _
            exact mul_nonneg (by rw [gA_apply]; positivity) (χA_partial_nonneg _)
  linarith

/-- `∑_{n ≤ N} g(n) ≤ 2 N`. -/
private theorem partial_le (N : ℕ) : ∑ n ∈ Finset.Ioc 0 N, gN n ≤ 2 * N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    · have h1 := ih (N / 2) (Nat.div_lt_self hpos (by norm_num))
      have h2 := window_le N
      have h3 : ∑ n ∈ Finset.Ioc (N / 2) N, gN n ≤ N := by exact_mod_cast h2
      rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le (N / 2)) (Nat.div_le_self N 2)]
      have : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
      omega

/-- `Icc 1 N = Ioc 0 N`. -/
private theorem Icc_eq_Ioc (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n; simp; omega

/-- `χ₄` as a complex Dirichlet character -/
private noncomputable def χC : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- Values of `χC`. -/
private theorem χC_apply (n : ℕ) : χC (n : ZMod 4) = ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℂ) := by
  simp [χC, MulChar.ringHomComp_apply]

/-- `χ₄` is not the trivial character. -/
private theorem χC_ne_one : χC ≠ 1 := by
  intro h
  have h3 : χC ((3 : ℕ) : ZMod 4) = 1 := by
    rw [h]; apply MulChar.one_apply
    rw [ZMod.isUnit_iff_coprime]; norm_num
  rw [χC_apply, ZMod.χ₄_nat_three_mod_four (by norm_num)] at h3
  norm_num at h3

/-- The trivial character mod `4` is the indicator of odd numbers. -/
private theorem one_char_apply (n : ℕ) : (1 : DirichletCharacter ℂ 4) (n : ZMod 4) = if Odd n then 1 else 0 := by
  have hu : IsUnit (n : ZMod 4) ↔ Odd n := by
    rw [ZMod.isUnit_iff_coprime, show (4 : ℕ) = 2 ^ 2 by norm_num,
      Nat.coprime_pow_right_iff (by norm_num), Nat.coprime_two_right]
  by_cases h : Odd n
  · rw [if_pos h, MulChar.one_apply (hu.mpr h)]
  · rw [if_neg h, MulChar.map_nonunit _ (fun h' => h (hu.mp h'))]

/-- The L-series of `g` converges absolutely for `re s > 1`. -/
private theorem LSeriesSummable_g {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => (gN n : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO (r := 1) ?_ zero_le_one (by simpa using hs)
  refine Asymptotics.IsBigO.of_bound 2 (Filter.Eventually.of_forall fun n => ?_)
  simp only [Complex.norm_natCast, Real.rpow_one, Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity), abs_of_nonneg (by positivity),
    Icc_eq_Ioc]
  exact_mod_cast partial_le n

/-- `L(g, s) L(s, χ₄) = L(s, χ₀)` for `re s > 1`. -/
private theorem LSeries_identity {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (gN n : ℂ)) s * DirichletCharacter.LFunction χC s =
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 4) s := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs, DirichletCharacter.LFunction_eq_LSeries _ hs]
  have hg : LSeries (fun n => (gN n : ℂ)) s = LSeries ↗(gA : ArithmeticFunction ℂ) s :=
    LSeries_congr (fun {n} _ => by simp [intCoe_apply, gA_apply]) s
  have hχ : LSeries (fun n => χC n) s = LSeries ↗(χA : ArithmeticFunction ℂ) s :=
    LSeries_congr (fun {n} hn => by simp [intCoe_apply, χA_apply hn, χC_apply]) s
  have ho : LSeries (fun n => (1 : DirichletCharacter ℂ 4) n) s =
      LSeries ↗(oA : ArithmeticFunction ℂ) s :=
    LSeries_congr (fun {n} _ => by
      rw [one_char_apply, intCoe_apply, oA_apply]; split_ifs <;> simp) s
  have hsg : LSeriesSummable ↗(gA : ArithmeticFunction ℂ) s :=
    (LSeriesSummable_congr s (fun {n} _ => by simp [intCoe_apply, gA_apply])).mp
      (LSeriesSummable_g hs)
  have hsχ : LSeriesSummable ↗(χA : ArithmeticFunction ℂ) s :=
    (LSeriesSummable_congr s (fun {n} hn => by simp [intCoe_apply, χA_apply hn, χC_apply])).mp
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χC hs)
  rw [hg, hχ, ho, ← ArithmeticFunction.LSeries_mul' hsg hsχ, ← intCoe_mul, gA_mul_χA]

/-- the paired terms of the L-series of `χ₄` -/
private noncomputable def uu (σ : ℝ) (m : ℕ) : ℝ := ((4 * m + 1 : ℝ) ^ σ)⁻¹ - ((4 * m + 3 : ℝ) ^ σ)⁻¹

/-- `∑ (4m + k)^{-σ}` converges for `σ > 1`. -/
private theorem summable_shift {σ : ℝ} (hσ : 1 < σ) (k : ℝ) (hk : 1 ≤ k) :
    Summable (fun m : ℕ => ((4 * m + k : ℝ) ^ σ)⁻¹) := by
  have h1 : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ σ)⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hσ)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) h1
  apply inv_anti₀ (by positivity)
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

/-- For real `σ > 1`, `L(σ, χ₄) = ∑ ((4m+1)^{-σ} - (4m+3)^{-σ})`. -/
private theorem LSeries_χC_real {σ : ℝ} (hσ : 1 < σ) :
    LSeries (fun n => χC n) σ = ((∑' m, uu σ m : ℝ) : ℂ) := by
  have hsum : Summable (LSeries.term (fun n => χC n) σ) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χC (by simpa using hσ)
  rw [LSeries, Nat.sumByResidueClasses hsum 4]
  rw [show (∑ j : ZMod 4, ∑' m, LSeries.term (fun n => χC n) σ (j.val + 4 * m)) =
    ∑' m, LSeries.term (fun n => χC n) σ (0 + 4 * m) + ∑' m, LSeries.term (fun n => χC n) σ (1 + 4 * m) +
    ∑' m, LSeries.term (fun n => χC n) σ (2 + 4 * m) + ∑' m, LSeries.term (fun n => χC n) σ (3 + 4 * m)
    from Fin.sum_univ_four (fun j : Fin 4 => ∑' m, LSeries.term (fun n => χC n) σ (j.val + 4 * m))]
  have hcp : ∀ n : ℕ, (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    intro n; rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
  have h0 : ∀ m : ℕ, LSeries.term (fun n => χC n) σ (0 + 4 * m) = 0 := by
    intro m
    rw [LSeries.term_def]; split_ifs with h
    · rfl
    · rw [χC_apply, ZMod.χ₄_nat_eq_if_mod_four, if_pos (by omega)]; simp
  have h2 : ∀ m : ℕ, LSeries.term (fun n => χC n) σ (2 + 4 * m) = 0 := by
    intro m
    rw [LSeries.term_def]; split_ifs with h
    · rfl
    · rw [χC_apply, ZMod.χ₄_nat_eq_if_mod_four, if_pos (by omega)]; simp
  have h1 : ∀ m : ℕ, LSeries.term (fun n => χC n) σ (1 + 4 * m) =
      ((((4 * m + 1 : ℝ) ^ σ)⁻¹ : ℝ) : ℂ) := by
    intro m
    rw [LSeries.term_def, if_neg (by omega), χC_apply, ZMod.χ₄_nat_one_mod_four (by omega), hcp]
    push_cast; ring_nf
  have h3 : ∀ m : ℕ, LSeries.term (fun n => χC n) σ (3 + 4 * m) =
      -((((4 * m + 3 : ℝ) ^ σ)⁻¹ : ℝ) : ℂ) := by
    intro m
    rw [LSeries.term_def, if_neg (by omega), χC_apply, ZMod.χ₄_nat_three_mod_four (by omega), hcp]
    push_cast; ring_nf
  simp_rw [h0, h1, h2, h3, tsum_zero, zero_add, add_zero, tsum_neg, ← Complex.ofReal_tsum]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_add, ← sub_eq_add_neg,
    ← (summable_shift hσ 1 le_rfl).tsum_sub (summable_shift hσ 3 (by norm_num))]
  rfl

/-- The paired terms are nonnegative. -/
private theorem uu_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) : 0 ≤ uu σ m := by
  unfold uu
  rw [sub_nonneg]
  apply inv_anti₀ (by positivity)
  exact Real.rpow_le_rpow (by positivity) (by linarith) hσ

/-- Uniform bound `0 ≤ uu σ m ≤ 4 / (m + 1)²` for `1 ≤ σ ≤ 2`. -/
private theorem uu_le {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) (m : ℕ) : uu σ m ≤ 4 * (((m + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
  unfold uu
  set a : ℝ := 4 * m + 1 with ha
  set b : ℝ := 4 * m + 3 with hb
  have ha1 : 1 ≤ a := by rw [ha]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hb1 : 0 < b := by rw [hb]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hab : b = a + 2 := by rw [ha, hb]; ring
  -- Bernoulli
  have hbern : 1 + σ * (a / b - 1) ≤ (a / b) ^ σ := by
    have := one_add_mul_self_le_rpow_one_add (s := a / b - 1) (by
      have : 0 ≤ a / b := by positivity
      linarith) h1
    simpa using this
  rw [Real.div_rpow (by linarith) hb1.le] at hbern
  have haσ : 0 < a ^ σ := by positivity
  have hbσ : 0 < b ^ σ := by positivity
  have hkey : (a ^ σ)⁻¹ - (b ^ σ)⁻¹ = (a ^ σ)⁻¹ * (1 - a ^ σ / b ^ σ) := by
    field_simp
  rw [hkey]
  have hinv : (a ^ σ)⁻¹ ≤ a⁻¹ := by
    apply inv_anti₀ (by linarith)
    calc a = a ^ (1:ℝ) := (Real.rpow_one a).symm
      _ ≤ a ^ σ := Real.rpow_le_rpow_of_exponent_le ha1 h1
  have hfac : 1 - a ^ σ / b ^ σ ≤ σ * (2 / b) := by
    have : a / b - 1 = -(2 / b) := by rw [hab]; field_simp; ring
    rw [this] at hbern; linarith
  have hfac0 : 0 ≤ 1 - a ^ σ / b ^ σ := by
    rw [sub_nonneg, div_le_one hbσ]
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  calc (a ^ σ)⁻¹ * (1 - a ^ σ / b ^ σ) ≤ a⁻¹ * (σ * (2 / b)) :=
        mul_le_mul hinv hfac hfac0 (by positivity)
    _ ≤ a⁻¹ * (2 * (2 / a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul h2 _ (by positivity) (by norm_num)
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    _ = 4 * (a ^ 2)⁻¹ := by field_simp; ring
    _ ≤ 4 * (((m + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply inv_anti₀ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        rw [ha]; push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

/-- The paired terms at `σ = 1`. -/
private theorem uu_one (m : ℕ) : uu 1 m = 1 / (4 * m + 1) - 1 / (4 * m + 3) := by
  simp [uu, Real.rpow_one]

/-- Partial sums of the paired terms are partial sums of the Leibniz series. -/
private theorem partial_uu (K : ℕ) : ∑ m ∈ Finset.range K, uu 1 m =
    ∑ i ∈ Finset.range (2 * K), (-1 : ℝ) ^ i / (2 * i + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (K + 1) = 2 * K + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, uu_one]
    rw [pow_succ, pow_mul]
    push_cast
    ring

/-- `∑ (1/(4m+1) - 1/(4m+3)) = π / 4`. -/
private theorem tsum_uu_one : ∑' m, uu 1 m = Real.pi / 4 := by
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg (uu_nonneg zero_le_one)]
  simp_rw [partial_uu]
  exact Real.tendsto_sum_pi_div_four.comp
    (Filter.tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))

/-- `∑ uu σ m → π / 4` as `σ → 1⁺` (dominated convergence). -/
private theorem tendsto_tsum_uu :
    Filter.Tendsto (fun σ : ℝ => ∑' m, uu σ m) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (Real.pi / 4)) := by
  rw [← tsum_uu_one]
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => 4 * (((m + 1 : ℕ) : ℝ) ^ 2)⁻¹)
    ?_ ?_ ?_
  · refine Summable.mul_left 4 ?_
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
    exact this
  · intro m
    have hc : ContinuousAt (fun σ : ℝ => uu σ m) 1 := by
      unfold uu
      apply ContinuousAt.sub
      · exact ((continuousAt_const.rpow continuousAt_id (Or.inl (by positivity))).inv₀
          (by positivity))
      · exact ((continuousAt_const.rpow continuousAt_id (Or.inl (by positivity))).inv₀
          (by positivity))
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · have : Set.Ioo (1:ℝ) 2 ∈ nhdsWithin (1:ℝ) (Set.Ioi 1) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with σ hσ
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg (uu_nonneg (by linarith [hσ.1]) m)]
    exact uu_le hσ.1.le hσ.2.le m

/-- `L(1, χ₄) = π / 4`. -/
private theorem LFunction_χC_one : DirichletCharacter.LFunction χC 1 = (Real.pi / 4 : ℝ) := by
  have hcont : ContinuousAt (DirichletCharacter.LFunction χC) 1 :=
    (DirichletCharacter.differentiableAt_LFunction χC 1 (Or.inr χC_ne_one)).continuousAt
  have h1 : Filter.Tendsto (fun σ : ℝ => DirichletCharacter.LFunction χC σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (DirichletCharacter.LFunction χC 1)) := by
    have : Filter.Tendsto (fun σ : ℝ => (σ : ℂ)) (nhdsWithin 1 (Set.Ioi 1)) (nhds ((1:ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    rw [Complex.ofReal_one] at this
    exact hcont.tendsto.comp this
  have h2 : Filter.Tendsto (fun σ : ℝ => DirichletCharacter.LFunction χC σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((Real.pi / 4 : ℝ) : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto _).comp tendsto_tsum_uu
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Function.comp]
    rw [DirichletCharacter.LFunction_eq_LSeries _ (by simpa using hσ), LSeries_χC_real hσ]
  exact tendsto_nhds_unique h1 h2

/-- the holomorphic function `T(s) / (s L(s, χ₄))`, where `T(s) = (s - 1) L(s, χ₀)` -/
private noncomputable def HH (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ 4 s / (s * DirichletCharacter.LFunction χC s)

/-- `(s - 1) L(s, χ₀)` at `s = 1` equals `1 / 2`. -/
private theorem T_one : DirichletCharacter.LFunctionTrivChar₁ 4 1 = 1 / 2 := by
  simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_self]
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  norm_num

/-- `HH 1 = 2 / π`. -/
private theorem HH_one : HH 1 = ((2 / Real.pi : ℝ) : ℂ) := by
  rw [HH, T_one, LFunction_χC_one, one_mul]
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  norm_num

/-- The set where `s ≠ 0` and `L(s, χ₄) ≠ 0` is open. -/
private theorem open_U : IsOpen {s : ℂ | s ≠ 0 ∧ DirichletCharacter.LFunction χC s ≠ 0} := by
  apply IsOpen.inter (isOpen_ne)
  exact isOpen_ne_fun (DirichletCharacter.differentiable_LFunction χC_ne_one).continuous
    continuous_const

/-- The closed half plane `re s ≥ 1` lies in that open set. -/
private theorem half_plane_sub_U : {s : ℂ | 1 ≤ s.re} ⊆ {s : ℂ | s ≠ 0 ∧ DirichletCharacter.LFunction χC s ≠ 0} := by
  intro s hs
  refine ⟨fun h => ?_, DirichletCharacter.LFunction_ne_zero_of_one_le_re χC (Or.inl χC_ne_one) hs⟩
  rw [h] at hs; simp at hs; linarith

/-- `HH` is holomorphic on that open set. -/
private theorem differentiableOn_HH :
    DifferentiableOn ℂ HH {s : ℂ | s ≠ 0 ∧ DirichletCharacter.LFunction χC s ≠ 0} := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ 4 s
  · exact differentiableAt_id.mul (DirichletCharacter.differentiable_LFunction χC_ne_one s)
  · exact mul_ne_zero hs.1 hs.2

/-- `dslope HH 1` is continuous on `re s ≥ 1`. -/
private theorem continuousOn_G : ContinuousOn (dslope HH 1) {s : ℂ | 1 ≤ s.re} := by
  have hU : {s : ℂ | s ≠ 0 ∧ DirichletCharacter.LFunction χC s ≠ 0} ∈ nhds (1 : ℂ) :=
    open_U.mem_nhds (half_plane_sub_U (by simp))
  have := (Complex.differentiableOn_dslope hU).mpr differentiableOn_HH
  exact this.continuousOn.mono half_plane_sub_U

/-- `L(g, s) / s - (2/π) / (s - 1) = dslope HH 1 s` for `re s > 1`. -/
private theorem G_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((gN n : ℝ) : ℂ)) s / s - ((2 / Real.pi : ℝ) : ℂ) / (s - 1) = dslope HH 1 s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hL : DirichletCharacter.LFunction χC s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χC (Or.inl χC_ne_one) hs.le
  have hid := LSeries_identity hs
  have hT : DirichletCharacter.LFunctionTrivChar₁ 4 s =
      (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 4) s := by
    simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
  have hg : LSeries (fun n => ((gN n : ℝ) : ℂ)) s = LSeries (fun n => (gN n : ℂ)) s := by
    congr 1
  rw [dslope_of_ne _ hs1, slope_def_field, ← HH_one, hg]
  unfold HH
  rw [hT, ← hid]
  field_simp

end Arith

namespace Fin1

open Filter Topology

/-- `⌊J / k⌋ / J → 1 / k` -/
private theorem tendsto_div_nat_div (k : ℕ) (hk : 0 < k) :
    Tendsto (fun J : ℕ => ((J / k : ℕ) : ℝ) / J) atTop (𝓝 (1 / k)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hup : ∀ J : ℕ, ((J / k : ℕ) : ℝ) / J ≤ 1 / k := by
    intro J
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · simp
    · have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
      rw [div_le_div_iff₀ hJ' hk', one_mul]
      have := Nat.cast_div_le (m := J) (n := k) (α := ℝ)
      rw [le_div_iff₀ hk'] at this
      linarith
  have hlow : ∀ J : ℕ, 0 < J → 1 / k - 1 / J ≤ ((J / k : ℕ) : ℝ) / J := by
    intro J hJ
    have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
    have h1 : (J : ℝ) < ((J / k : ℕ) + 1) * k := by
      have := Nat.lt_div_mul_add (a := J) hk
      exact_mod_cast (by linarith [this] : J < (J / k + 1) * k)
    rw [div_sub_div _ _ hk'.ne' hJ'.ne', div_le_div_iff₀ (by positivity) hJ']
    nlinarith
  have hlim : Tendsto (fun J : ℕ => 1 / (k : ℝ) - 1 / J) atTop (𝓝 (1 / k)) := by
    have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (tendsto_const_nhds (x := 1 / (k : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_
    (Eventually.of_forall hup)
  filter_upwards [eventually_gt_atTop 0] with J hJ using hlow J hJ

/-- `J / k → ∞`. -/
private theorem tendsto_div_nat_atTop (k : ℕ) (hk : 0 < k) : Tendsto (fun J : ℕ => J / k) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b * k, fun J hJ => ?_⟩
  exact (Nat.le_div_iff_mul_le hk).mpr hJ

/-- composition: if `R M / M → c` then `R (J / k) / J → c / k` -/
private theorem tendsto_comp_div (R : ℕ → ℝ) (hR0 : R 0 = 0) {c : ℝ}
    (hRlim : Tendsto (fun M : ℕ => R M / M) atTop (𝓝 c)) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun J : ℕ => R (J / k) / J) atTop (𝓝 (c * (1 / k))) := by
  have h1 := (hRlim.comp (tendsto_div_nat_atTop k hk)).mul (tendsto_div_nat_div k hk)
  refine h1.congr (fun J => ?_)
  simp only [Function.comp]
  by_cases hM : J / k = 0
  · rw [hM, hR0]; simp
  · have hM' : ((J / k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hM
    field_simp

/-- If `R(M)/M → c` with `0 ≤ R(M) ≤ C M`, then `(∑ᵢ R(J / 2^i)) / J → 2 c`. -/
private theorem dyadic (R : ℕ → ℝ) (C c : ℝ) (hR0 : R 0 = 0) (hRnn : ∀ M, 0 ≤ R M)
    (hRle : ∀ M, R M ≤ C * M) (hRlim : Tendsto (fun M : ℕ => R M / M) atTop (𝓝 c)) :
    Tendsto (fun J : ℕ => (∑' i : ℕ, R (J / 2 ^ i)) / J) atTop (𝓝 (2 * c)) := by
  have hC : 0 ≤ C := by have := hRle 1; have := hRnn 1; simp at *; linarith
  have hsum : Summable (fun i : ℕ => C * (1 / 2 : ℝ) ^ i) :=
    (summable_geometric_two).mul_left C
  have hlim : Tendsto (fun J : ℕ => ∑' i : ℕ, R (J / 2 ^ i) / J) atTop
      (𝓝 (∑' i : ℕ, c * (1 / 2 : ℝ) ^ i)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun i => ?_) ?_
    · have := tendsto_comp_div R hR0 hRlim (2 ^ i) (pow_pos (by norm_num) i)
      simpa [one_div, inv_pow] using this
    · refine Eventually.of_forall fun J i => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hRnn _) (Nat.cast_nonneg _))]
      rcases Nat.eq_zero_or_pos J with rfl | hJ
      · simp; positivity
      have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
      rw [div_le_iff₀ hJ']
      calc R (J / 2 ^ i) ≤ C * ((J / 2 ^ i : ℕ) : ℝ) := hRle _
        _ ≤ C * ((J : ℝ) / 2 ^ i) := by
            apply mul_le_mul_of_nonneg_left _ hC
            have := Nat.cast_div_le (m := J) (n := 2 ^ i) (α := ℝ)
            simpa using this
        _ = C * (1 / 2) ^ i * J := by rw [one_div, inv_pow]; field_simp
  rw [tsum_mul_left, tsum_geometric_two, mul_comm] at hlim
  refine hlim.congr (fun J => ?_)
  rw [tsum_div_const]

end Fin1

namespace Comb

open Math0.Statements.A354571

/-- number of coprime ordered factorizations `N = x * y` -/
private def UU (N : ℕ) : ℕ := ((Nat.divisorsAntidiagonal N).filter (fun p => Nat.Coprime p.1 p.2)).card

/-- number of coprime factorizations `N = x * y` with `x < y` -/
private def UC (N : ℕ) : ℕ :=
  ((Nat.divisorsAntidiagonal N).filter (fun p => Nat.Coprime p.1 p.2 ∧ p.1 < p.2)).card

/-- `UU 1 = 1`. -/
private theorem UU_one : UU 1 = 1 := by decide

/-- `UU (p^n a) = 2 UU a` for `p ∤ a`. -/
private theorem UU_prime_pow_mul {p a n : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hn : 0 < n) :
    UU (p ^ n * a) = 2 * UU a := by
  classical
  have ha0 : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero p)
  have hpn : 0 < p ^ n := pow_pos hp.pos n
  have hpa0 : p ^ n * a ≠ 0 := Nat.mul_ne_zero hpn.ne' ha0
  set A := (Nat.divisorsAntidiagonal a).filter (fun q => Nat.Coprime q.1 q.2) with hA
  set f₁ : ℕ × ℕ → ℕ × ℕ := fun q => (p ^ n * q.1, q.2) with hf₁
  set f₂ : ℕ × ℕ → ℕ × ℕ := fun q => (q.1, p ^ n * q.2) with hf₂
  have hinj₁ : Function.Injective f₁ := by
    intro x y h
    simp only [hf₁, Prod.mk.injEq] at h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hpn h.1) h.2
  have hinj₂ : Function.Injective f₂ := by
    intro x y h
    simp only [hf₂, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Nat.eq_of_mul_eq_mul_left hpn h.2)
  have hcopn : ∀ y, y ∣ a → Nat.Coprime (p ^ n) y := by
    intro y hy
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hpa (h.trans hy))
  have hS : (Nat.divisorsAntidiagonal (p ^ n * a)).filter (fun q => Nat.Coprime q.1 q.2) =
      A.image f₁ ∪ A.image f₂ := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_union,
      Finset.mem_image, hA, hf₁, hf₂, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨⟨huv, -⟩, hcop⟩
      have hpuv : p ∣ u * v := by rw [huv]; exact Dvd.dvd.mul_right (dvd_pow_self p hn.ne') a
      rcases (Nat.Prime.dvd_mul hp).mp hpuv with hpu | hpv
      · have hpv : ¬ p ∣ v := fun h =>
          (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left hpu hcop) h
        have hcv : Nat.Coprime (p ^ n) v :=
          Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpv)
        have hdvd : p ^ n ∣ u := hcv.dvd_of_dvd_mul_right (by rw [huv]; exact dvd_mul_right _ _)
        obtain ⟨x, rfl⟩ := hdvd
        have hxv : x * v = a := by
          apply Nat.eq_of_mul_eq_mul_left hpn; rw [← huv]; ring
        left
        exact ⟨x, v, ⟨⟨hxv, ha0⟩, Nat.Coprime.coprime_mul_left hcop⟩, rfl, rfl⟩
      · have hpu : ¬ p ∣ u := fun h =>
          (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_right hpv hcop).symm h
        have hcu : Nat.Coprime (p ^ n) u :=
          Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpu)
        have hdvd : p ^ n ∣ v := hcu.dvd_of_dvd_mul_left (by rw [huv]; exact dvd_mul_right _ _)
        obtain ⟨y, rfl⟩ := hdvd
        have huy : u * y = a := by
          apply Nat.eq_of_mul_eq_mul_left hpn; rw [← huv]; ring
        right
        exact ⟨u, y, ⟨⟨huy, ha0⟩, Nat.Coprime.coprime_mul_left_right hcop⟩, rfl, rfl⟩
    · rintro (⟨x, y, ⟨⟨hxy, -⟩, hcop⟩, rfl, rfl⟩ | ⟨x, y, ⟨⟨hxy, -⟩, hcop⟩, rfl, rfl⟩)
      · refine ⟨⟨by rw [← hxy]; ring, hpa0⟩, ?_⟩
        exact Nat.Coprime.mul_left (hcopn y (Dvd.intro_left x hxy)) hcop
      · refine ⟨⟨by rw [← hxy]; ring, hpa0⟩, ?_⟩
        exact Nat.Coprime.mul_right (hcopn x (Dvd.intro y hxy)).symm hcop
  have hdisj : Disjoint (A.image f₁) (A.image f₂) := by
    rw [Finset.disjoint_left]
    rintro q h1 h2
    simp only [Finset.mem_image, hA, Finset.mem_filter, Nat.mem_divisorsAntidiagonal,
      hf₁, hf₂, Prod.exists] at h1 h2
    obtain ⟨x, y, ⟨⟨hxy, -⟩, -⟩, rfl⟩ := h1
    obtain ⟨x', y', ⟨⟨hxy', -⟩, -⟩, h⟩ := h2
    simp only [Prod.mk.injEq] at h
    apply hpa
    rw [← hxy', h.1]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self p hn.ne') x) y'
  unfold UU
  rw [hS, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj₁,
    Finset.card_image_of_injective _ hinj₂, ← hA]
  ring

/-- `UU N = 2^{ω(N)}`. -/
private theorem UU_eq (N : ℕ) (hN : N ≠ 0) : UU N = 2 ^ N.primeFactors.card := by
  induction N using Nat.recOnPrimePow with
  | zero => exact absurd rfl hN
  | one => simp [UU_one]
  | prime_pow_mul a p n hp hpa hn ih =>
    have ha0 : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero p)
    rw [UU_prime_pow_mul hp hpa hn, ih ha0, Nat.primeFactors_mul (pow_pos hp.pos n).ne' ha0,
      Nat.primeFactors_prime_pow hn.ne' hp, Finset.card_union_of_disjoint, Finset.card_singleton,
      pow_add, pow_one, mul_comm]
    rw [Finset.disjoint_singleton_left]
    exact fun h => hpa (Nat.dvd_of_mem_primeFactors h)

/-- `UU N = 2 UC N + [N = 1]`. -/
private theorem UU_eq_UC (N : ℕ) : UU N = 2 * UC N + (if N = 1 then 1 else 0) := by
  classical
  by_cases hN1 : N = 1
  · subst hN1; decide
  rw [if_neg hN1, add_zero]
  set S := (Nat.divisorsAntidiagonal N).filter (fun p => Nat.Coprime p.1 p.2) with hS
  have hUC : UC N = (S.filter (fun q => q.1 < q.2)).card := by
    rw [UC, hS, Finset.filter_filter]
  have h1 : S.filter (fun q => ¬ q.1 < q.2) = S.filter (fun q => q.2 < q.1) := by
    ext ⟨x, y⟩
    simp only [hS, Finset.mem_filter, Nat.mem_divisorsAntidiagonal, not_lt]
    constructor
    · rintro ⟨⟨⟨hxy, hN0⟩, hcop⟩, hle⟩
      refine ⟨⟨⟨hxy, hN0⟩, hcop⟩, lt_of_le_of_ne hle ?_⟩
      rintro rfl
      have : y = 1 := by rwa [Nat.Coprime, Nat.gcd_self] at hcop
      subst this; exact hN1 (by rw [← hxy])
    · rintro ⟨h, hlt⟩; exact ⟨h, hlt.le⟩
  have h2 : (S.filter (fun q => q.2 < q.1)).card = (S.filter (fun q => q.1 < q.2)).card := by
    apply Finset.card_nbij' Prod.swap Prod.swap
    · rintro ⟨x, y⟩ h
      rw [Finset.mem_coe] at h ⊢
      simp only [hS, Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Prod.swap_prod_mk] at h ⊢
      exact ⟨⟨⟨by rw [mul_comm]; exact h.1.1.1, h.1.1.2⟩, h.1.2.symm⟩, h.2⟩
    · rintro ⟨x, y⟩ h
      rw [Finset.mem_coe] at h ⊢
      simp only [hS, Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Prod.swap_prod_mk] at h ⊢
      exact ⟨⟨⟨by rw [mul_comm]; exact h.1.1.1, h.1.1.2⟩, h.1.2.symm⟩, h.2⟩
    · intro q _; rfl
    · intro q _; rfl
  have h3 := Finset.card_filter_add_card_filter_not (s := S) (fun q => q.1 < q.2)
  rw [h1, h2] at h3
  rw [UU, ← hS, ← h3, hUC]; ring

/-- In a primitive triple, the leg `b` and the hypotenuse `c` are coprime. -/
private theorem ppt_coprime {b k c : ℕ} (h : IsPPT b k c) : Nat.Coprime b c := by
  obtain ⟨hb, hk, heq, hg⟩ := h
  set g := Nat.gcd b c with hgdef
  have hgb : g ∣ b := Nat.gcd_dvd_left b c
  have hgc : g ∣ c := Nat.gcd_dvd_right b c
  have hg2 : g ^ 2 ∣ k ^ 2 := by
    have h1 : g ^ 2 ∣ c ^ 2 := pow_dvd_pow_of_dvd hgc 2
    have h2 : g ^ 2 ∣ b ^ 2 := pow_dvd_pow_of_dvd hgb 2
    have : k ^ 2 = c ^ 2 - b ^ 2 := by omega
    rw [this]; exact Nat.dvd_sub h1 h2
  have hgk : g ∣ k := (Nat.pow_dvd_pow_iff two_ne_zero).mp hg2
  have : g ∣ Nat.gcd (Nat.gcd b k) c := Nat.dvd_gcd (Nat.dvd_gcd hgb hgk) hgc
  rw [hg] at this
  exact Nat.dvd_one.mp this

/-- A coprime leg/hypotenuse pair gives a primitive triple. -/
private theorem ppt_of {b k c : ℕ} (hb : 0 < b) (hk : 0 < k) (heq : b ^ 2 + k ^ 2 = c ^ 2)
    (hcop : Nat.Coprime b c) : IsPPT b k c := by
  refine ⟨hb, hk, heq, ?_⟩
  exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left b k) hcop

/-- The leg is smaller than the hypotenuse. -/
private theorem ppt_lt {b k c : ℕ} (h : IsPPT b k c) : b < c := by
  obtain ⟨hb, hk, heq, -⟩ := h
  have : b ^ 2 < c ^ 2 := by have : 0 < k ^ 2 := by positivity
                             omega
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this

/-- If the given leg is even, the other leg and the hypotenuse are odd. -/
private theorem ppt_even_leg_odd {b n c : ℕ} (h : IsPPT b (2 * n) c) : Odd b ∧ Odd c := by
  have hcop := ppt_coprime h
  obtain ⟨hb, hk, heq, -⟩ := h
  have hk2 : Even ((2 * n) ^ 2) := (Nat.even_pow' two_ne_zero).mpr (even_two_mul n)
  have hbo : Odd b := by
    rw [← Nat.not_even_iff_odd]
    intro hbe
    have hce : Even c := by
      have : Even (c ^ 2) := by
        rw [← heq]; exact Even.add ((Nat.even_pow' two_ne_zero).mpr hbe) hk2
      exact (Nat.even_pow' two_ne_zero).mp this
    have h2 : 2 ∣ Nat.gcd b c := Nat.dvd_gcd (even_iff_two_dvd.mp hbe) (even_iff_two_dvd.mp hce)
    rw [hcop] at h2
    omega
  refine ⟨hbo, ?_⟩
  have : Odd (c ^ 2) := by rw [← heq]; exact Odd.add_even (hbo.pow) hk2
  exact (Nat.odd_pow_iff two_ne_zero).mp this

/-- For odd `k`, the triangles with leg `k` correspond to `k² = d e`, `d < e` coprime. -/
private theorem card_leg_odd {k : ℕ} (hk : Odd k) : (legTriangles k).card = UC (k ^ 2) := by
  unfold UC
  apply Finset.card_nbij' (fun q => (q.2 - q.1, q.2 + q.1)) (fun q => ((q.2 - q.1) / 2, (q.2 + q.1) / 2))
  · rintro ⟨b, c⟩ h
    rw [Finset.mem_coe, mem_legTriangles] at h
    rw [Finset.mem_coe]
    have hbc := ppt_lt h
    have hcop := ppt_coprime h
    obtain ⟨hb, hk0, heq, -⟩ := h
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    have hprod : (c - b) * (c + b) = k ^ 2 := by
      zify [hbc.le] at heq ⊢
      linear_combination (-1 : ℤ) * heq
    refine ⟨⟨hprod, by positivity⟩, ?_, by omega⟩
    set g := Nat.gcd (c - b) (c + b) with hg
    have h1 : g ∣ 2 * c := by
      have := Nat.dvd_add (Nat.gcd_dvd_left (c - b) (c + b)) (Nat.gcd_dvd_right (c - b) (c + b))
      rwa [show c - b + (c + b) = 2 * c by omega] at this
    have h2 : g ∣ 2 * b := by
      have := Nat.dvd_sub (Nat.gcd_dvd_right (c - b) (c + b)) (Nat.gcd_dvd_left (c - b) (c + b))
      rwa [show c + b - (c - b) = 2 * b by omega] at this
    have h3 : g ∣ 2 := by
      have := Nat.dvd_gcd h2 h1
      rwa [Nat.gcd_mul_left, hcop, mul_one] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
    · exact h
    · exfalso
      have h4 : 2 ∣ k ^ 2 := by
        rw [← hprod]; exact Dvd.dvd.mul_right (h ▸ Nat.gcd_dvd_left (c - b) (c + b)) _
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h4
      rw [← even_iff_two_dvd] at this
      exact (Nat.not_even_iff_odd.mpr hk) this
  · rintro ⟨d, e⟩ h
    rw [Finset.mem_coe] at h
    rw [Finset.mem_coe]
    show ((e - d) / 2, (e + d) / 2) ∈ legTriangles k
    rw [mem_legTriangles]
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at h
    obtain ⟨⟨hde, -⟩, hcop, hlt⟩ := h
    have hodd : Odd (d * e) := by rw [hde]; exact hk.pow
    obtain ⟨hdo, heo⟩ := Nat.odd_mul.mp hodd
    rw [Nat.odd_iff] at hdo heo
    obtain ⟨b, rfl⟩ : ∃ b, e = d + 2 * b := ⟨(e - d) / 2, by omega⟩
    rw [show (d + 2 * b - d) / 2 = b by omega, show (d + 2 * b + d) / 2 = d + b by omega]
    have hcbd : Nat.Coprime d b := (Nat.coprime_self_add_right.mp hcop).coprime_mul_left_right
    refine ppt_of (by omega) hk.pos ?_ (Nat.coprime_add_self_right.mpr hcbd.symm)
    rw [← hde]; ring
  · rintro ⟨b, c⟩ h
    rw [Finset.mem_coe, mem_legTriangles] at h
    have := ppt_lt h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨d, e⟩ h
    rw [Finset.mem_coe] at h
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at h
    obtain ⟨⟨hde, -⟩, hcop, hlt⟩ := h
    have hodd : Odd (d * e) := by rw [hde]; exact hk.pow
    obtain ⟨hdo, heo⟩ := Nat.odd_mul.mp hodd
    rw [Nat.odd_iff] at hdo heo
    simp only [Prod.mk.injEq]
    omega

/-- No primitive triangle has a leg `≡ 2 (mod 4)`. -/
private theorem leg_two_mul_odd {n : ℕ} (hn : Odd n) : legTriangles (2 * n) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨b, c⟩ h
  rw [mem_legTriangles] at h
  obtain ⟨hbo, hco⟩ := ppt_even_leg_odd h
  obtain ⟨-, -, heq, -⟩ := h
  obtain ⟨u, rfl⟩ := hbo
  obtain ⟨w, rfl⟩ := hco
  have h1 : u * (u + 1) + n * n = w * (w + 1) := by nlinarith
  have hu := Nat.even_mul_succ_self u
  have hw := Nat.even_mul_succ_self w
  have hnn : Even (n * n) := by
    rw [← h1] at hw
    exact (Nat.even_add.mp hw).mp hu
  rcases Nat.even_mul.mp hnn with h | h <;> exact (Nat.not_even_iff_odd.mpr hn) h

/-- For even `n`, the triangles with leg `2n` correspond to `n² = d e`, `d < e` coprime. -/
private theorem card_leg_even {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    (legTriangles (2 * n)).card = UC (n ^ 2) := by
  unfold UC
  apply Finset.card_nbij' (fun q => ((q.2 - q.1) / 2, (q.2 + q.1) / 2)) (fun q => (q.2 - q.1, q.2 + q.1))
  · rintro ⟨b, c⟩ h
    rw [Finset.mem_coe, mem_legTriangles] at h
    rw [Finset.mem_coe]
    have hbc := ppt_lt h
    have hcop := ppt_coprime h
    obtain ⟨hbo, hco⟩ := ppt_even_leg_odd h
    obtain ⟨hb, hk0, heq, -⟩ := h
    rw [Nat.odd_iff] at hbo hco
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    obtain ⟨d, hd⟩ : ∃ d, c = b + 2 * d := ⟨(c - b) / 2, by omega⟩
    subst hd
    rw [show (b + 2 * d - b) / 2 = d by omega, show (b + 2 * d + b) / 2 = b + d by omega]
    have hprod : d * (b + d) = n ^ 2 := by nlinarith
    refine ⟨⟨hprod, by positivity⟩, ?_, by omega⟩
    -- coprime d (b + d)
    have h1 : Nat.Coprime b (b + 2 * d) := hcop
    have h2 : Nat.Coprime b (2 * d) := Nat.coprime_self_add_right.mp h1
    have h3 : Nat.Coprime b d := h2.coprime_mul_left_right
    exact Nat.coprime_add_self_right.mpr h3.symm
  · rintro ⟨d, e⟩ h
    rw [Finset.mem_coe] at h
    rw [Finset.mem_coe]
    show (e - d, e + d) ∈ legTriangles (2 * n)
    rw [mem_legTriangles]
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at h
    obtain ⟨⟨hde, -⟩, hcop, hlt⟩ := h
    have hev : Even (d * e) := by rw [hde]; exact (Nat.even_pow' two_ne_zero).mpr hn
    have hpar : d % 2 + e % 2 = 1 := by
      rcases Nat.even_mul.mp hev with h | h
      · have : ¬ Even e := fun h' => by
          have h2 : 2 ∣ Nat.gcd d e := Nat.dvd_gcd (even_iff_two_dvd.mp h) (even_iff_two_dvd.mp h')
          rw [hcop] at h2; omega
        rw [Nat.not_even_iff_odd, Nat.odd_iff] at this
        rw [Nat.even_iff] at h; omega
      · have : ¬ Even d := fun h' => by
          have h2 : 2 ∣ Nat.gcd d e := Nat.dvd_gcd (even_iff_two_dvd.mp h') (even_iff_two_dvd.mp h)
          rw [hcop] at h2; omega
        rw [Nat.not_even_iff_odd, Nat.odd_iff] at this
        rw [Nat.even_iff] at h; omega
    refine ppt_of (by omega) (by omega) ?_ ?_
    · zify [hlt.le]
      have : ((d : ℤ) * e) = (n : ℤ) ^ 2 := by exact_mod_cast hde
      linear_combination (-4) * this
    · set g := Nat.gcd (e - d) (e + d) with hg
      have h1 : g ∣ 2 * e := by
        have := Nat.dvd_add (Nat.gcd_dvd_left (e - d) (e + d)) (Nat.gcd_dvd_right (e - d) (e + d))
        rwa [show e - d + (e + d) = 2 * e by omega] at this
      have h2 : g ∣ 2 * d := by
        have := Nat.dvd_sub (Nat.gcd_dvd_right (e - d) (e + d)) (Nat.gcd_dvd_left (e - d) (e + d))
        rwa [show e + d - (e - d) = 2 * d by omega] at this
      have h3 : g ∣ 2 := by
        have := Nat.dvd_gcd h2 h1
        rwa [Nat.gcd_mul_left, hcop, mul_one] at this
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
      · exact h
      · exfalso
        have h4 : 2 ∣ e - d := h ▸ Nat.gcd_dvd_left (e - d) (e + d)
        omega
  · rintro ⟨b, c⟩ h
    rw [Finset.mem_coe, mem_legTriangles] at h
    have := ppt_lt h
    obtain ⟨hbo, hco⟩ := ppt_even_leg_odd h
    rw [Nat.odd_iff] at hbo hco
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨d, e⟩ h
    rw [Finset.mem_coe] at h
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at h
    obtain ⟨⟨hde, -⟩, hcop, hlt⟩ := h
    simp only [Prod.mk.injEq]
    omega

/-- `2 UC (k²) + [k = 1] = 2^{ω(k)}`. -/
private theorem two_UC_sq {k : ℕ} (hk : k ≠ 0) :
    2 * UC (k ^ 2) + (if k = 1 then 1 else 0) = 2 ^ k.primeFactors.card := by
  have h1 := UU_eq_UC (k ^ 2)
  rw [UU_eq _ (pow_ne_zero 2 hk), Nat.primeFactors_pow _ two_ne_zero] at h1
  rw [h1]
  congr 1
  simp only [sq_eq_one]

/-- `2 wO(k) + [k = 1] = g(k)`. -/
private theorem wO_eq (k : ℕ) : 2 * wO k + (if k = 1 then 1 else 0) = Arith.gN k := by
  unfold wO Arith.gN
  by_cases h : Odd k ∧ CondO k
  · rw [if_pos h, if_pos (show Odd k ∧ ∀ p ∈ k.primeFactors, p % 4 = 3 from h), card_leg_odd h.1]
    exact two_UC_sq (by rintro rfl; exact (Nat.not_odd_zero h.1))
  · rw [if_neg h, if_neg (show ¬ (Odd k ∧ ∀ p ∈ k.primeFactors, p % 4 = 3) from h), if_neg]
    rintro rfl
    exact h ⟨odd_one, by simp [CondO]⟩

/-- `wE k = 0` unless `4 ∣ k`. -/
private theorem wE_of_mod {k : ℕ} (hk : k % 4 ≠ 0) : wE k = 0 := by
  unfold wE
  split_ifs with h
  · obtain ⟨⟨r, hr⟩, -⟩ := h
    have hn : Odd r := by rw [Nat.odd_iff]; omega
    rw [show k = 2 * r by omega, leg_two_mul_odd hn, Finset.card_empty]
  · rfl

/-- Prime factors of `2 m` for even `m`. -/
private theorem primeFactors_two_mul_of_even {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) :
    (2 * m).primeFactors = m.primeFactors := by
  rw [Nat.primeFactors_mul two_ne_zero hm0, Nat.Prime.primeFactors Nat.prime_two]
  apply Finset.union_eq_right.mpr
  rw [Finset.singleton_subset_iff, Nat.mem_primeFactors]
  exact ⟨Nat.prime_two, even_iff_two_dvd.mp hm, hm0⟩

/-- Prime factors of `2 m` for odd `m`. -/
private theorem primeFactors_two_mul_of_odd {m : ℕ} (hm : Odd m) :
    (2 * m).primeFactors = {2} ∪ m.primeFactors := by
  rw [Nat.primeFactors_mul two_ne_zero (by rintro rfl; exact Nat.not_odd_zero hm),
    Nat.Prime.primeFactors Nat.prime_two]

/-- `wE (8 i) = wE (4 i)`. -/
private theorem wE_eight (i : ℕ) : wE (8 * i) = wE (4 * i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rfl
  have hpf : (8 * i).primeFactors = (4 * i).primeFactors := by
    rw [show 8 * i = 2 * (4 * i) by ring]
    exact primeFactors_two_mul_of_even ⟨2 * i, by ring⟩ (by omega)
  have hpf2 : (4 * i).primeFactors = (2 * i).primeFactors := by
    rw [show 4 * i = 2 * (2 * i) by ring]
    exact primeFactors_two_mul_of_even ⟨i, by ring⟩ (by omega)
  have hc8 : (legTriangles (8 * i)).card = (legTriangles (4 * i)).card := by
    rw [show 8 * i = 2 * (4 * i) by ring, card_leg_even ⟨2 * i, by ring⟩ (by omega),
      show 4 * i = 2 * (2 * i) by ring, card_leg_even ⟨i, by ring⟩ (by omega)]
    have h1 := two_UC_sq (k := 4 * i) (by omega)
    have h2 := two_UC_sq (k := 2 * i) (by omega)
    rw [if_neg (by omega)] at h1 h2
    rw [show 2 * (2 * i) = 4 * i by ring] at *
    rw [hpf2] at h1
    omega
  have hiff : (Even (8 * i) ∧ CondE (8 * i)) ↔ (Even (4 * i) ∧ CondE (4 * i)) := by
    unfold CondE
    rw [hpf]
    constructor
    · rintro ⟨-, h⟩; exact ⟨⟨2 * i, by ring⟩, h⟩
    · rintro ⟨-, h⟩; exact ⟨⟨4 * i, by ring⟩, h⟩
  unfold wE
  by_cases h : Even (4 * i) ∧ CondE (4 * i)
  · rw [if_pos (hiff.mpr h), if_pos h, hc8]
  · rw [if_neg (mt hiff.mp h), if_neg h]

/-- `wE (4 j) + [j = 1] = g(j)` for odd `j`. -/
private theorem wE_odd {j : ℕ} (hj : Odd j) : wE (4 * j) + (if j = 1 then 1 else 0) = Arith.gN j := by
  have hj0 : j ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hj
  have hpf4 : (4 * j).primeFactors = {2} ∪ j.primeFactors := by
    rw [show 4 * j = 2 * (2 * j) by ring, primeFactors_two_mul_of_even ⟨j, by ring⟩ (by omega),
      primeFactors_two_mul_of_odd hj]
  have hcard : (legTriangles (4 * j)).card = 2 ^ j.primeFactors.card := by
    rw [show 4 * j = 2 * (2 * j) by ring, card_leg_even ⟨j, by ring⟩ (by omega)]
    have h1 := two_UC_sq (k := 2 * j) (by omega)
    rw [if_neg (by omega), primeFactors_two_mul_of_odd hj, Finset.card_union_of_disjoint, Finset.card_singleton] at h1
    · rw [pow_add] at h1; omega
    · rw [Finset.disjoint_singleton_left, Nat.mem_primeFactors]
      rintro ⟨-, h2, -⟩
      exact (Nat.not_even_iff_odd.mpr hj) (even_iff_two_dvd.mpr h2)
  have hodd_pf : ∀ p ∈ j.primeFactors, Odd p := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    exact Odd.of_dvd_nat hj hp.2.1
  have hcond : CondE (4 * j) ↔ (∀ p ∈ j.primeFactors, p % 4 = 3) ∧ j ≠ 1 := by
    unfold CondE
    rw [hpf4]
    constructor
    · rintro ⟨h1, ⟨p, hp, hpo⟩⟩
      refine ⟨fun q hq => h1 q (Finset.mem_union_right _ hq) (hodd_pf q hq), ?_⟩
      rintro rfl
      simp at hp
      rw [hp] at hpo
      exact (Nat.not_odd_iff_even.mpr even_two) hpo
    · rintro ⟨h1, hne⟩
      refine ⟨fun q hq hqo => ?_, ?_⟩
      · rcases Finset.mem_union.mp hq with hq | hq
        · rw [Finset.mem_singleton] at hq; rw [hq] at hqo
          exact absurd hqo (Nat.not_odd_iff_even.mpr even_two)
        · exact h1 q hq
      · obtain ⟨p, hp⟩ : (j.primeFactors).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty, Ne, Nat.primeFactors_eq_empty]; omega
        exact ⟨p, Finset.mem_union_right _ hp, hodd_pf p hp⟩
  unfold wE Arith.gN
  by_cases h : (∀ p ∈ j.primeFactors, p % 4 = 3) ∧ j ≠ 1
  · rw [if_pos (show Even (4 * j) ∧ CondE (4 * j) from ⟨⟨2 * j, by ring⟩, hcond.mpr h⟩),
      if_pos (show Odd j ∧ ∀ p ∈ j.primeFactors, p % 4 = 3 from ⟨hj, h.1⟩), if_neg h.2, hcard,
      add_zero]
  · rw [if_neg (show ¬ (Even (4 * j) ∧ CondE (4 * j)) from fun h' => h (hcond.mp h'.2)), zero_add]
    by_cases h1 : j = 1
    · subst h1; simp
    · rw [if_neg h1, if_neg (show ¬ (Odd j ∧ ∀ p ∈ j.primeFactors, p % 4 = 3) from
        fun h' => h ⟨h'.2, h1⟩)]

/-- partial sums of `Arith.gN` -/
private def SN (N : ℕ) : ℕ := ∑ k ∈ Finset.range (N + 1), Arith.gN k

/-- partial sums of `wE (4 j)` -/
private def EE (J : ℕ) : ℕ := ∑ j ∈ Finset.range (J + 1), wE (4 * j)

/-- Recursion step for `EE`. -/
private theorem EE_succ (J : ℕ) : EE (J + 1) = EE J + wE (4 * (J + 1)) := Finset.sum_range_succ _ _

/-- Recursion step for `SN`. -/
private theorem SN_succ (J : ℕ) : SN (J + 1) = SN J + Arith.gN (J + 1) := Finset.sum_range_succ _ _

/-- `wE 0 = 0`. -/
private theorem wE_zero : wE 0 = 0 := by
  simp [wE, CondE]

/-- `g` vanishes on even numbers. -/
private theorem gN_of_even {k : ℕ} (hk : Even k) : Arith.gN k = 0 := by
  unfold Arith.gN
  rw [if_neg]
  rintro ⟨h, -⟩
  exact (Nat.not_odd_iff_even.mpr hk) h

/-- `2 numLE wO N + [N ≥ 1] = SN N`. -/
private theorem numLE_wO (N : ℕ) : 2 * numLE wO N + (if 1 ≤ N then 1 else 0) = SN N := by
  unfold numLE SN
  rw [Finset.mul_sum]
  have : (if 1 ≤ N then 1 else 0) = ∑ k ∈ Finset.range (N + 1), (if k = 1 then 1 else 0) := by
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    split_ifs <;> omega
  rw [this, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => wO_eq k

/-- `numLE wE N = EE (N / 4)`. -/
private theorem numLE_wE (N : ℕ) : numLE wE N = EE (N / 4) := by
  induction N with
  | zero => simp [numLE, EE, wE_zero]
  | succ N ih =>
    rw [numLE, Finset.sum_range_succ, ← numLE, ih]
    by_cases h : (N + 1) % 4 = 0
    · rw [show (N + 1) / 4 = N / 4 + 1 by omega, EE_succ,
        show 4 * (N / 4 + 1) = N + 1 by omega]
    · rw [wE_of_mod h, add_zero, show (N + 1) / 4 = N / 4 by omega]

/-- `EE J + [J ≥ 1] = SN J + EE (J / 2)`. -/
private theorem EE_rec (J : ℕ) : EE J + (if 1 ≤ J then 1 else 0) = SN J + EE (J / 2) := by
  induction J with
  | zero => simp [EE, SN, wE_zero, Arith.gN]
  | succ J ih =>
    rw [EE_succ, SN_succ]
    rcases Nat.even_or_odd (J + 1) with he | ho
    · rw [gN_of_even he]
      obtain ⟨r, hr⟩ := he
      have h1 : (J + 1) / 2 = J / 2 + 1 := by omega
      rw [h1, EE_succ, show 4 * (J + 1) = 8 * (J / 2 + 1) by omega, wE_eight]
      rw [if_pos (by omega)] at ih ⊢
      omega
    · have h1 := wE_odd ho
      have h2 : (J + 1) / 2 = J / 2 := by obtain ⟨r, hr⟩ := ho; omega
      rw [h2]
      split_ifs at ih h1 ⊢ <;> omega

/-- inverting the counting function -/
private theorem nth_limit (w : ℕ → ℕ) {L : ℝ} (hL : 0 < L)
    (hlim : Filter.Tendsto (fun N : ℕ => (numLE w N : ℝ) / N) Filter.atTop (nhds L))
    (hex : ∀ n, ∃ k, n ≤ numLE w k) :
    Filter.Tendsto (fun n : ℕ => (nthTerm w n : ℝ) / n) Filter.atTop (nhds L⁻¹) := by
  have hspec := fun n => nthTerm_spec w (hex n)
  -- nthTerm → ∞
  have hinf : Filter.Tendsto (nthTerm w) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro K
    refine ⟨numLE w K + 1, fun n hn => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h1 := (hspec n).1
    have h2 := numLE_mono w hlt.le
    omega
  have hup : Filter.Tendsto (fun n : ℕ => (numLE w (nthTerm w n) : ℝ) / (nthTerm w n))
      Filter.atTop (nhds L) := hlim.comp hinf
  have hsub : Filter.Tendsto (fun n : ℕ => nthTerm w n - 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_sub_atTop_nat 1 |>.comp hinf
  have hratio : Filter.Tendsto (fun n : ℕ => ((nthTerm w n - 1 : ℕ) : ℝ) / (nthTerm w n))
      Filter.atTop (nhds 1) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (nthTerm w n)) Filter.atTop (nhds 1) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hinf
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
    refine h0.congr' ?_
    filter_upwards [hinf.eventually (Filter.eventually_ge_atTop 1)] with n hn
    have : (0 : ℝ) < nthTerm w n := by exact_mod_cast hn
    rw [Nat.cast_sub hn, Nat.cast_one]
    field_simp
  have hlow : Filter.Tendsto (fun n : ℕ => (numLE w (nthTerm w n - 1) : ℝ) / (nthTerm w n))
      Filter.atTop (nhds L) := by
    have := (hlim.comp hsub).mul hratio
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hinf.eventually (Filter.eventually_ge_atTop 2)] with n hn
    simp only [Function.comp]
    have : ((nthTerm w n - 1 : ℕ) : ℝ) ≠ 0 := by
      have : 1 ≤ nthTerm w n - 1 := by omega
      exact_mod_cast (by omega : nthTerm w n - 1 ≠ 0)
    field_simp
  have hmain : Filter.Tendsto (fun n : ℕ => (n : ℝ) / (nthTerm w n)) Filter.atTop (nhds L) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hinf.eventually (Filter.eventually_ge_atTop 1)] with n hn
      have hpos : (0 : ℝ) < nthTerm w n := by exact_mod_cast hn
      apply div_le_div_of_nonneg_right _ hpos.le
      have := (hspec n).2 (nthTerm w n - 1) (by omega)
      exact_mod_cast this.le
    · filter_upwards [hinf.eventually (Filter.eventually_ge_atTop 1)] with n hn
      have hpos : (0 : ℝ) < nthTerm w n := by exact_mod_cast hn
      apply div_le_div_of_nonneg_right _ hpos.le
      exact_mod_cast (hspec n).1
  have := hmain.inv₀ hL.ne'
  refine this.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [inv_div]

end Comb

namespace Final

open Filter Topology Math0.Statements.A354571

/-- The partial sums `SN N` agree with the sums used in the Tauberian theorem. -/
private theorem SN_eq_Ioc (N : ℕ) : Comb.SN N = ∑ n ∈ Finset.Ioc 0 N, Arith.gN n := by
  induction N with
  | zero => simp [Comb.SN, Arith.gN_zero]
  | succ N ih => rw [Comb.SN_succ, ih, Finset.sum_Ioc_succ_top (Nat.zero_le N)]

/-- `SN N ≤ 2 N`. -/
private theorem SN_le (N : ℕ) : Comb.SN N ≤ 2 * N := by
  rw [SN_eq_Ioc]; exact Arith.partial_le N

/-- The main asymptotic `SN N / N → 2 / π`, from the Tauberian theorem. -/
private theorem SN_tendsto : Tendsto (fun N : ℕ => (Comb.SN N : ℝ) / N) atTop (𝓝 (2 / Real.pi)) := by
  have hM : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, (Arith.gN n : ℝ) ≤ 2 * N := by
    intro N
    rw [Arith.Icc_eq_Ioc]
    exact_mod_cast Arith.partial_le N
  have h := Tauber.tauberian (a := fun n => (Arith.gN n : ℝ)) (M := 2) (by norm_num)
    (fun n => Nat.cast_nonneg _) hM (2 / Real.pi) (by positivity) (dslope Arith.HH 1)
    Arith.continuousOn_G (fun s hs => Arith.G_eq hs)
  refine h.congr (fun N => ?_)
  rw [SN_eq_Ioc, Arith.Icc_eq_Ioc]
  push_cast
  rfl

/-- `numLE wO N / N → 1 / π`. -/
private theorem wO_tendsto : Tendsto (fun N : ℕ => (numLE wO N : ℝ) / N) atTop (𝓝 (1 / Real.pi)) := by
  have h1 : Tendsto (fun N : ℕ => ((Comb.SN N : ℝ) / N - 1 / N) / 2) atTop
      (𝓝 ((2 / Real.pi - 0) / 2)) :=
    (SN_tendsto.sub tendsto_one_div_atTop_nhds_zero_nat).div_const 2
  rw [show (2 / Real.pi - 0) / 2 = 1 / Real.pi by ring] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have h := Comb.numLE_wO N
  rw [if_pos hN] at h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : (Comb.SN N : ℝ) = 2 * numLE wO N + 1 := by exact_mod_cast h.symm
  rw [this]; field_simp; ring

/-- The summand of the dyadic decomposition of `EE`. -/
private noncomputable def RR (M : ℕ) : ℝ := (Comb.SN M : ℝ) - (if 1 ≤ M then 1 else 0)

/-- `RR 0 = 0`. -/
private theorem RR_zero : RR 0 = 0 := by
  simp [RR, Comb.SN, Arith.gN_zero]

/-- `RR` is nonnegative. -/
private theorem RR_nonneg (M : ℕ) : 0 ≤ RR M := by
  unfold RR
  split_ifs with h
  · have : 1 ≤ Comb.SN M := by
      unfold Comb.SN
      calc 1 = Arith.gN 1 := Arith.gN_one.symm
        _ ≤ ∑ k ∈ Finset.range (M + 1), Arith.gN k :=
          Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have : (1 : ℝ) ≤ Comb.SN M := by exact_mod_cast this
    linarith
  · simp

/-- `RR M ≤ 2 M`. -/
private theorem RR_le (M : ℕ) : RR M ≤ 2 * M := by
  unfold RR
  have : (Comb.SN M : ℝ) ≤ 2 * M := by exact_mod_cast SN_le M
  split_ifs <;> linarith

/-- `RR M / M → 2 / π`. -/
private theorem RR_tendsto : Tendsto (fun M : ℕ => RR M / M) atTop (𝓝 (2 / Real.pi)) := by
  have h := SN_tendsto.sub tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  unfold RR
  rw [if_pos hM, sub_div]

/-- The recursion for `EE` over the reals. -/
private theorem EE_real (J : ℕ) : (Comb.EE J : ℝ) = RR J + Comb.EE (J / 2) := by
  have h := Comb.EE_rec J
  have h' : (Comb.EE J : ℝ) + (if 1 ≤ J then 1 else 0) = Comb.SN J + Comb.EE (J / 2) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast at this
    split_ifs at this ⊢ <;> simpa using this
  unfold RR
  linarith

/-- The dyadic decomposition `EE J = ∑ᵢ RR (J / 2^i)`. -/
private theorem EE_tsum (J : ℕ) : (Comb.EE J : ℝ) = ∑' i : ℕ, RR (J / 2 ^ i) := by
  induction J using Nat.strong_induction_on with
  | _ J ih =>
    have hsum : Summable (fun i : ℕ => RR (J / 2 ^ i)) := by
      apply summable_of_ne_finset_zero (s := Finset.range (J + 1))
      intro i hi
      rw [Finset.mem_range, not_lt] at hi
      have : J < 2 ^ i := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.div_eq_of_lt this, RR_zero]
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · simp [Comb.EE, Comb.wE_zero, RR_zero]
    rw [hsum.tsum_eq_zero_add, EE_real, ih (J / 2) (Nat.div_lt_self hJ (by norm_num))]
    simp only [pow_zero, Nat.div_one]
    congr 1
    refine tsum_congr fun i => ?_
    rw [Nat.div_div_eq_div_mul, pow_succ']

/-- `EE J / J → 4 / π`. -/
private theorem EE_tendsto : Tendsto (fun J : ℕ => (Comb.EE J : ℝ) / J) atTop (𝓝 (2 * (2 / Real.pi))) := by
  have := Fin1.dyadic RR 2 (2 / Real.pi) RR_zero RR_nonneg RR_le RR_tendsto
  refine this.congr (fun J => ?_)
  rw [EE_tsum]

/-- `numLE wE N / N → 1 / π`. -/
private theorem wE_tendsto : Tendsto (fun N : ℕ => (numLE wE N : ℝ) / N) atTop (𝓝 (1 / Real.pi)) := by
  have h := Fin1.tendsto_comp_div (fun J => (Comb.EE J : ℝ))
    (by simp [Comb.EE, Comb.wE_zero]) EE_tendsto 4 (by norm_num)
  rw [show 2 * (2 / Real.pi) * (1 / ((4 : ℕ) : ℝ)) = 1 / Real.pi by push_cast; ring] at h
  refine h.congr (fun N => ?_)
  rw [Comb.numLE_wE]

end Final

open Math0.Statements.A354571 in
/-- Selle's conjecture holds: `a(n)/n → π` for A354571 and A354570. -/
theorem result : statement := by
  have hpi : (1 / Real.pi)⁻¹ = Real.pi := by rw [one_div, inv_inv]
  have hL : (0 : ℝ) < 1 / Real.pi := by positivity
  refine ⟨?_, ?_⟩
  · have h := Comb.nth_limit wE hL Final.wE_tendsto exists_le_numLE_wE
    rw [hpi] at h
    exact h
  · have h := Comb.nth_limit wO hL Final.wO_tendsto exists_le_numLE_wO
    rw [hpi] at h
    exact h

end Math0.Frontier.A354571

#math0_settles Math0.Frontier.A354571.result Math0.Statements.A354571.statement
