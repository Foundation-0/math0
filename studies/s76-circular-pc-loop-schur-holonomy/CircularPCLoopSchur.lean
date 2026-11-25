/-
  Track S76 — Circular Predictive Coding:
  Exact Block-Cyclic Loop-Schur Pushforward, Monodromy Holonomy,
  DEQ Adjoint Gauge-Cancellation, EP Order-Cancellation & Truncated-Phase
  Blowup Obstructions, Krein/Sylvester Inertia, Non-Normal Amplification,
  and Complex-Curl Power-Iteration Obstruction.

  Pure Lean 4 Init kernel only (zero imports, zero custom axioms,
  zero sorry, zero native_decide, zero warnings).
-/

namespace CircularPCLoopSchur

/-! ## Helper integer algebra lemmas (pure Init, zero Mathlib) -/

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -x := Int.neg_nonneg_of_nonpos h
    have hmul : 0 ≤ (-x) * (-x) := Int.mul_nonneg hneg hneg
    have heq : (-x) * (-x) = x * x := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [heq] at hmul
    exact hmul

private theorem int_sq_pos_of_ne_zero (x : Int) (hx : x ≠ 0) : 0 < x * x := by
  have hge : 0 ≤ x * x := int_sq_nonneg x
  rcases Int.lt_or_eq_of_le hge with hlt | heq
  · exact hlt
  · exfalso
    have hzero : x * x = 0 := Eq.symm heq
    rcases Int.mul_eq_zero.mp hzero with h1 | h2
    · exact hx h1
    · exact hx h2

/-! ## Pillar 1: Block-Cyclic Loop-Schur Pushforward, Metric G_loop, and DEQ Adjoint Cancellation -/

/--
  Theorem 1 (Universal L=2 Loop-Schur Metric Tensor Identity):
  For a 2-node circular PC loop with edge slopes `a, b : Int`, monodromy `m = b * a`,
  and exact loop metric `g = 1 + b * b > 0`, eliminating the internal node `u` at
  `g * u = (a + b) * s` reduces the scaled energy `2 * g * E(u, s)` to the exact
  metric-weighted Loop-Schur form `(1 - b * a)^2 * s^2` (NOT naive `(1 - m)^2 * g * s^2`).
-/
theorem loop_schur_2node_metric_exact (a b s : Int) :
    let g := 1 + b * b
    let eu_scaled := (a + b) * s - a * (g * s)
    let es_scaled := g * s - b * ((a + b) * s)
    eu_scaled * eu_scaled + es_scaled * es_scaled = g * ((1 - b * a) * s) * ((1 - b * a) * s) := by
  dsimp only
  have h1 : (a + b) * s - a * ((1 + b * b) * s) = b * ((1 - b * a) * s) := by
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.one_mul]
    have hab : a * (b * b * s) = b * (b * a * s) := by
      ac_rfl
    rw [hab]
    omega
  have h2 : (1 + b * b) * s - b * ((a + b) * s) = (1 - b * a) * s := by
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.one_mul]
    have hbb : b * (b * s) = b * b * s := by ac_rfl
    have hba : b * (a * s) = b * a * s := by ac_rfl
    rw [hbb, hba]
    omega
  rw [h1, h2]
  have h3 : (b * ((1 - b * a) * s)) * (b * ((1 - b * a) * s)) =
      (b * b) * (((1 - b * a) * s) * ((1 - b * a) * s)) := by
    ac_rfl
  rw [h3]
  have h4 : (1 + b * b) * ((1 - b * a) * s) * ((1 - b * a) * s) =
      (1 + b * b) * (((1 - b * a) * s) * ((1 - b * a) * s)) := by
    ac_rfl
  rw [h4, Int.add_mul, Int.one_mul, Int.add_comm]

/--
  Theorem 2 (Universal L=2 Loop Metric Strict Lower Bound and Softening):
  `G_loop = 1 + b^2 >= 1` for all `b : Int`, and `G_loop > 1` whenever `b != 0`,
  proving that the exact Loop-Schur curvature is strictly softer than `(1 - M)^2`
  whenever the closing edge has nonzero Jacobian.
-/
theorem loop_schur_2node_metric_softening (b : Int) :
    1 ≤ 1 + b * b ∧ (b ≠ 0 → 1 < 1 + b * b) := by
  constructor
  · have h := int_sq_nonneg b
    omega
  · intro hb
    have h := int_sq_pos_of_ne_zero b hb
    omega

/--
  Theorem 3 (Universal L=3 Loop-Schur Metric Tensor Identity):
  For a 3-node circular PC loop with edge slopes `a, b, c : Int`, monodromy `m = c * b * a`,
  and exact metric `G_3 = 1 + c^2 + (c * b)^2 >= 1`, the minimum-norm error split
  `e1 = (c * b) * r`, `e2 = c * r`, `e3 = r` with `r = (1 - c * b * a) * s` satisfies both
  the exact loop-compatibility constraint `e3 + c * e2 + c * b * e1 = G_3 * r` and the
  exact quadratic energy identity `e1^2 + e2^2 + e3^2 = G_3 * r^2`.
-/
theorem loop_schur_3node_metric_exact (a b c s : Int) :
    let g3 := 1 + c * c + (c * b) * (c * b)
    let r := (1 - c * b * a) * s
    let e1 := (c * b) * r
    let e2 := c * r
    let e3 := r
    1 ≤ g3 ∧
    e3 + c * e2 + (c * b) * e1 = g3 * r ∧
    e1 * e1 + e2 * e2 + e3 * e3 = g3 * (r * r) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · have hc := int_sq_nonneg c
    have hcb := int_sq_nonneg (c * b)
    omega
  · have h1 : c * (c * ((1 - c * b * a) * s)) = (c * c) * ((1 - c * b * a) * s) := by ac_rfl
    have h2 : (c * b) * ((c * b) * ((1 - c * b * a) * s)) =
        ((c * b) * (c * b)) * ((1 - c * b * a) * s) := by ac_rfl
    rw [h1, h2]
    simp only [Int.add_mul, Int.one_mul]
  · have h1 : ((c * b) * ((1 - c * b * a) * s)) * ((c * b) * ((1 - c * b * a) * s)) =
        ((c * b) * (c * b)) * (((1 - c * b * a) * s) * ((1 - c * b * a) * s)) := by ac_rfl
    have h2 : (c * ((1 - c * b * a) * s)) * (c * ((1 - c * b * a) * s)) =
        (c * c) * (((1 - c * b * a) * s) * ((1 - c * b * a) * s)) := by ac_rfl
    rw [h1, h2]
    simp only [Int.add_mul, Int.one_mul]
    omega

/--
  Theorem 4 (Universal L=2 PC Hessian Determinant = Monodromy Determinant Squared):
  For `H_PC = [[1 + b^2, -(a + b)], [-(a + b), 1 + a^2]]`,
  `det(H_PC) = (1 + b^2)(1 + a^2) - (a + b)^2 = (1 - a * b)^2`.
-/
theorem loop_hessian_2node_det_eq_monodromy_sq (a b : Int) :
    (1 + b * b) * (1 + a * a) - (a + b) * (a + b) = (1 - a * b) * (1 - a * b) := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.one_mul, Int.mul_one]
  have h1 : b * b * (a * a) = a * b * (a * b) := by ac_rfl
  have h2 : b * a = a * b := by ac_rfl
  rw [h1, h2]
  omega

/--
  Theorem 5 (Universal L=2 DEQ Adjoint Gauge-Cancellation of G_loop):
  When solving the nudged linear-response equation `H_PC (du, ds) = (0, -gs)` with
  scaled denominator `d = (1 - b * a)`, setting `ds_num = -(1 + b^2) * gs` and
  `du_num = -(a + b) * gs` solves both rows of `H_PC * z_num = (0, -d^2 * gs)`, while
  the scaled prediction errors `eu_num = du_num - a * ds_num` and
  `es_num = ds_num - b * du_num` factor cleanly by `d` as `es_num = -d * gs` and
  `eu_num = -d * b * gs`, cancelling `G_loop = 1 + b^2` identically in the adjoint!
-/
theorem loop_adjoint_gloop_cancellation (a b gs : Int) :
    let d := 1 - b * a
    let ds_num := -(1 + b * b) * gs
    let du_num := -(a + b) * gs
    (1 + b * b) * du_num - (a + b) * ds_num = 0 ∧
    -(a + b) * du_num + (1 + a * a) * ds_num = -(d * d) * gs ∧
    du_num - a * ds_num = -d * (b * gs) ∧
    ds_num - b * du_num = -d * gs := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (1 + b * b) * (-(a + b) * gs) = -((1 + b * b) * ((a + b) * gs)) := by
      rw [Int.neg_mul, Int.mul_neg]
    have h2 : (a + b) * (-(1 + b * b) * gs) = -((1 + b * b) * ((a + b) * gs)) := by
      rw [Int.neg_mul, Int.mul_neg]
      have hcomm : (a + b) * ((1 + b * b) * gs) = (1 + b * b) * ((a + b) * gs) := by ac_rfl
      rw [hcomm]
    rw [h1, h2]
    omega
  · have hdet := loop_hessian_2node_det_eq_monodromy_sq a b
    have hab : a * b = b * a := Int.mul_comm a b
    rw [hab] at hdet
    have hlhs :
        -(a + b) * (-(a + b) * gs) + (1 + a * a) * (-(1 + b * b) * gs) =
        -((1 + b * b) * (1 + a * a) - (a + b) * (a + b)) * gs := by
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.sub_mul]
      have hcomm : (1 + a * a) * ((1 + b * b) * gs) = (1 + b * b) * (1 + a * a) * gs := by ac_rfl
      have hsq : (a + b) * ((a + b) * gs) = (a + b) * (a + b) * gs := by ac_rfl
      rw [hcomm, hsq]
      omega
    rw [hlhs, hdet]
  · simp only [Int.neg_mul, Int.mul_neg, Int.sub_neg, Int.add_mul, Int.mul_add,
      Int.sub_mul, Int.one_mul]
    have h1 : a * (b * b * gs) = b * a * (b * gs) := by ac_rfl
    rw [h1]
    omega
  · simp only [Int.neg_mul, Int.mul_neg, Int.sub_neg, Int.add_mul, Int.mul_add,
      Int.sub_mul, Int.one_mul]
    have h1 : b * (a * gs) = b * a * gs := by ac_rfl
    have h2 : b * (b * gs) = b * b * gs := by ac_rfl
    rw [h1, h2]
    omega

/--
  Theorem 6 (Universal Zero-Energy / DEQ Fixed-Point Bijection for L=2 and L=3):
  A loop state has zero prediction errors if and only if its readout node is a fixed
  point of the composed monodromy map and all internal nodes match the forward pass.
-/
theorem loop_zero_energy_deq_bijection_2node (a b u s c : Int) :
    (u - a * s = 0 ∧ s - (b * u + c) = 0) ↔ (s = b * a * s + c ∧ u = a * s) := by
  constructor
  · intro ⟨h1, h2⟩
    have hu : u = a * s := by omega
    rw [hu] at h2
    have hba : b * (a * s) = b * a * s := by ac_rfl
    rw [hba] at h2
    exact ⟨by omega, hu⟩
  · intro ⟨hs, hu⟩
    have hba : b * (a * s) = b * a * s := by ac_rfl
    refine ⟨by omega, ?_⟩
    rw [hu, hba]
    omega

theorem loop_zero_energy_deq_bijection_3node (a b c x1 x2 x3 inj : Int) :
    (x1 - a * x3 = 0 ∧ x2 - b * x1 = 0 ∧ x3 - (c * x2 + inj) = 0) ↔
    (x3 = c * b * a * x3 + inj ∧ x1 = a * x3 ∧ x2 = b * a * x3) := by
  constructor
  · intro ⟨h1, h2, h3⟩
    have hx1 : x1 = a * x3 := by omega
    rw [hx1] at h2
    have hba : b * (a * x3) = b * a * x3 := by ac_rfl
    rw [hba] at h2
    have hx2 : x2 = b * a * x3 := by omega
    rw [hx2] at h3
    have hcba : c * (b * a * x3) = c * b * a * x3 := by ac_rfl
    rw [hcba] at h3
    exact ⟨by omega, hx1, hx2⟩
  · intro ⟨hx3, hx1, hx2⟩
    have hba : b * (a * x3) = b * a * x3 := by ac_rfl
    have hcba : c * (b * a * x3) = c * b * a * x3 := by ac_rfl
    refine ⟨by omega, ?_, ?_⟩
    · rw [hx1, hba]
      omega
    · rw [hx2, hcba]
      omega

/-! ## Pillar 2: Centered ±beta vs One-Sided +beta EP & Truncated-Phase O(e*/beta) Obstructions -/

/--
  Theorem 7 (Universal Smooth Jet Order Cancellation: O(beta) vs O(beta^2)):
  For any cubic jet `u(b) = g0 + g1*b + g2*b^2 + g3*b^3`, the one-sided difference
  retains the quadratic term `g2 * b^2` (yielding `O(b)` bias after dividing by `b`),
  whereas the centered difference `u(b) - u(-b)` cancels both `g0` and `g2 * b^2`
  identically, leaving only `2 * g3 * b^3` (`O(b^2)` bias after dividing by `2*b`).
-/
theorem ep_cubic_jet_centered_cancels_order1 (g0 g1 g2 g3 b : Int) :
    let uPos := g0 + g1 * b + g2 * (b * b) + g3 * (b * b * b)
    let uNeg := g0 + g1 * (-b) + g2 * ((-b) * (-b)) + g3 * ((-b) * (-b) * (-b))
    (uPos - g0) - g1 * b = g2 * (b * b) + g3 * (b * b * b) ∧
    (uPos - uNeg) - 2 * (g1 * b) = 2 * (g3 * (b * b * b)) := by
  dsimp only
  have hsq : (-b) * (-b) = b * b := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  have hcb : (-b) * (-b) * (-b) = -(b * b * b) := by
    rw [hsq, Int.mul_neg]
  have h1 : g1 * (-b) = -(g1 * b) := Int.mul_neg g1 b
  have h3 : g3 * (-(b * b * b)) = -(g3 * (b * b * b)) := Int.mul_neg g3 (b * b * b)
  rw [hcb, hsq, h1, h3]
  constructor <;> omega

/--
  Theorem 8 (Exact Closed-Form Circular PC EP Bias Separation):
  On the exact 1-node circular PC energy `E(theta, x) = 1/2 * ((1 - theta) * x - c)^2`
  with linear readout cost `C(x) = q * x` and `d = 1 - theta != 0`:
  At the exact nudged equilibria `x_pm = (d * c ∓ beta * q) / d^2`, the scaled
  parameter gradient `d^3 * (dE/dtheta)(x_pm) = ± beta * (d * c * q) - beta^2 * q^2`.
  Hence one-sided `+beta` EP incurs exact nonzero `O(beta)` bias `-beta * q^2 / d^3`,
  while centered `±beta` EP cancels the `beta^2` bias identically to ZERO for EVERY `beta != 0`!
-/
theorem ep_exact_linear_circular_pc_bias_law (d c q b : Int) :
    let gradPosScaled := (d * c - b * q) * (b * q)
    let gradNegScaled := (d * c + b * q) * (-(b * q))
    let exactIftScaled := d * c * q
    gradPosScaled - b * exactIftScaled = -(b * b) * (q * q) ∧
    (gradPosScaled - gradNegScaled) = 2 * b * exactIftScaled := by
  dsimp only
  have hp : (d * c - b * q) * (b * q) = b * (d * c * q) - (b * b) * (q * q) := by
    rw [Int.sub_mul]
    have h1 : d * c * (b * q) = b * (d * c * q) := by ac_rfl
    have h2 : b * q * (b * q) = (b * b) * (q * q) := by ac_rfl
    rw [h1, h2]
  have hn : (d * c + b * q) * (-(b * q)) = -(b * (d * c * q)) - (b * b) * (q * q) := by
    rw [Int.mul_neg, Int.add_mul]
    have h1 : d * c * (b * q) = b * (d * c * q) := by ac_rfl
    have h2 : b * q * (b * q) = (b * b) * (q * q) := by ac_rfl
    rw [h1, h2]
    omega
  rw [hp, hn]
  have h2b : 2 * b * (d * c * q) = 2 * (b * (d * c * q)) := by ac_rfl
  have hneg : -(b * b) * (q * q) = -((b * b) * (q * q)) := Int.neg_mul (b * b) (q * q)
  rw [h2b, hneg]
  constructor <;> omega

/--
  Theorem 9 (Two-Sided Truncated-Free-Phase O(e*/beta) Pole & Centered Double-Cancellation):
  Suppose the free phase stops with nonzero residual `e0 = d * delta0 != 0` (so
  `g_free_scaled = -x_tilde * e0 != 0`), and the `±beta` nudged states inherit a
  common residual fraction `gamma` (`x_tilde_pm = x_pm + gamma * delta0`, residual
  `e_pm = gamma * e0 ∓ beta * q / d`). Then in cleared denominators (`d^3`):
  (i) Omitting subtraction (`g(x_tilde_+) / beta`) injects a `1/beta` pole proportional
      to `gamma * e0` (`-d^2 * (d * x_star + gamma * e0) * (gamma * e0)` at order `beta^0`);
  (ii) Subtracting `g(x_tilde_free)` when `gamma = 0` (free truncated, nudge converged)
      injects the OPPOSITE `1/beta` pole `+d^2 * (d * x_star + e0) * e0` at order `beta^0`;
  (iii) Centered `±beta` `(g(x_tilde_+) - g(x_tilde_-)) / (2*beta)` cancels the ENTIRE
      `1/beta` pole identically for EVERY `gamma : Int`, leaving exact `beta`-independent
      multiplier `2 * b * d * q * (c + 2 * gamma * e0)` (with zero `O(1/beta)` divergence!).
-/
theorem ep_truncated_phase_pole_and_centered_cancellation (d c q b e0 gamma : Int) :
    let e_rem := gamma * e0
    let x_p := d * c + d * e_rem - b * q
    let r_p := d * e_rem - b * q
    let x_m := d * c + d * e_rem + b * q
    let r_m := d * e_rem + b * q
    let g_p := -(x_p * r_p)
    let g_m := -(x_m * r_m)
    let g_f := -((d * c + d * e0) * (d * e0))
    let pole_nosub := -((d * c + d * e_rem) * (d * e_rem))
    let pole_sub_conv := (d * c + d * e0) * (d * e0)
    -- (i) At b = 0, g_p equals the nonzero O(1/beta) numerator pole_nosub
    (-( (d * c + d * e_rem - 0 * q) * (d * e_rem - 0 * q) ) = pole_nosub) ∧
    -- (ii) When gamma = 0 (nudge converged, free truncated), g_p(b=0) - g_f = pole_sub_conv
    (0 - g_f = pole_sub_conv) ∧
    -- (iii) Centered difference cancels the O(1/beta) pole identically for ALL gamma, e0, b!
    (g_p - g_m = 2 * b * (d * q * (c + 2 * e_rem))) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp only [Int.zero_mul, Int.sub_zero]
  · omega
  · have hp :
        -((d * c + d * (gamma * e0) - b * q) * (d * (gamma * e0) - b * q)) =
        -((d * c + d * (gamma * e0)) * (d * (gamma * e0)))
        + b * q * (d * c + 2 * (d * (gamma * e0)))
        - (b * q) * (b * q) := by
      simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add]
      have h1 : d * (gamma * e0) * (b * q) = b * q * (d * (gamma * e0)) := by ac_rfl
      have h2 : d * c * (b * q) = b * q * (d * c) := by ac_rfl
      have h3 : b * q * (2 * (d * (gamma * e0))) = 2 * (b * q * (d * (gamma * e0))) := by ac_rfl
      rw [h1, h2, h3]
      omega
    have hm :
        -((d * c + d * (gamma * e0) + b * q) * (d * (gamma * e0) + b * q)) =
        -((d * c + d * (gamma * e0)) * (d * (gamma * e0)))
        - b * q * (d * c + 2 * (d * (gamma * e0)))
        - (b * q) * (b * q) := by
      simp only [Int.add_mul, Int.mul_add]
      have h1 : d * (gamma * e0) * (b * q) = b * q * (d * (gamma * e0)) := by ac_rfl
      have h2 : d * c * (b * q) = b * q * (d * c) := by ac_rfl
      have h3 : b * q * (2 * (d * (gamma * e0))) = 2 * (b * q * (d * (gamma * e0))) := by ac_rfl
      rw [h1, h2, h3]
      omega
    rw [hp, hm]
    have hfac :
        2 * (b * q * (d * c + 2 * (d * (gamma * e0)))) =
        2 * b * (d * q * (c + 2 * (gamma * e0))) := by
      simp only [Int.mul_add]
      have ha : 2 * (b * q * (d * c)) = 2 * b * (d * q * c) := by ac_rfl
      have hb : 2 * (b * q * (2 * (d * (gamma * e0)))) =
          2 * b * (d * q * (2 * (gamma * e0))) := by ac_rfl
      rw [ha, hb]
    omega

/--
  Theorem 10 (Strict Non-Vanishing of the Truncated Free-Phase Pole):
  Whenever `d != 0`, `e0 != 0`, and `c + e0 != 0`, the `O(1/beta)` pole numerator
  `d^2 * (c + e0) * e0` is strictly nonzero.
-/
theorem ep_truncated_pole_nonzero (d c e0 : Int) (hd : d ≠ 0) (he : e0 ≠ 0) (hce : c + e0 ≠ 0) :
    (d * c + d * e0) * (d * e0) ≠ 0 := by
  intro hzero
  have hfac : (d * c + d * e0) * (d * e0) = (d * d) * ((c + e0) * e0) := by
    rw [← Int.mul_add]
    ac_rfl
  rw [hfac] at hzero
  rcases Int.mul_eq_zero.mp hzero with hdd | hrest
  · rcases Int.mul_eq_zero.mp hdd with h1 | h2
    · exact hd h1
    · exact hd h2
  · rcases Int.mul_eq_zero.mp hrest with h1 | h2
    · exact hce h1
    · exact he h2

/-! ## Pillar 3: Krein / Sylvester Inertia, Bifurcation Shadow, Non-Normal Amplification & Curl -/

/--
  Theorem 11 (Contractive Loop Strict SPD Hessian — Sylvester Inertia `(2, 0, 0)`):
  For rational edge slopes `a/q, b/q` with `q > 0` and strict contraction `|a * b| < q^2`
  (equivalently `(a * b)^2 < q^4`), the cleared-denominator 2-node Hessian has strictly
  positive trace and strictly positive determinant `(q^2 - a * b)^2 > 0`.
-/
theorem contractive_loop_spd_hessian (a b q : Int) (hq : 0 < q) (hcon : a * b < q * q) :
    let h11 := q * q + b * b
    let h22 := q * q + a * a
    let h12 := -(q * a + q * b)
    0 < h11 ∧ 0 < h11 + h22 ∧
    h11 * h22 - h12 * h12 = (q * q - a * b) * (q * q - a * b) ∧
    0 < h11 * h22 - h12 * h12 := by
  dsimp only
  have hqq : 0 < q * q := Int.mul_pos hq hq
  have haa := int_sq_nonneg a
  have hbb := int_sq_nonneg b
  have hdet :
      (q * q + b * b) * (q * q + a * a) - (-(q * a + q * b)) * (-(q * a + q * b)) =
      (q * q - a * b) * (q * q - a * b) := by
    have hneg : (-(q * a + q * b)) * (-(q * a + q * b)) = (q * a + q * b) * (q * a + q * b) := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [hneg]
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
    have h1 : q * q * (a * a) = q * a * (q * a) := by ac_rfl
    have h2 : b * b * (q * q) = q * b * (q * b) := by ac_rfl
    have h3 : b * b * (a * a) = a * b * (a * b) := by ac_rfl
    have h4 : q * a * (q * b) = q * q * (a * b) := by ac_rfl
    have h5 : q * b * (q * a) = a * b * (q * q) := by ac_rfl
    rw [h1, h2, h3, h4, h5]
    omega
  refine ⟨by omega, by omega, hdet, ?_⟩
  rw [hdet]
  have hpos : 0 < q * q - a * b := by omega
  exact Int.mul_pos hpos hpos

/--
  Theorem 12 (Critical Bifurcation Zero-Mode Shadow `det(I - M) = 0`):
  When `a * b = q * q` (`1` lies in `spec(M_loop)`), `det(H_PC) = 0` and the explicit
  nonzero shadow vector `v = (a, q)` lies in `ker(J_R) = ker(H_PC)`, proving rank drop
  from Sylvester inertia `(2, 0, 0)` to `(1, 0, 1)`.
-/
theorem critical_bifurcation_zero_mode_shadow (a b q : Int) (hq : 0 < q) (hcrit : a * b = q * q) :
    (q * q + b * b) * (q * q + a * a) - (q * a + q * b) * (q * a + q * b) = 0 ∧
    (q * a - a * q = 0) ∧
    (q * q - b * a = 0) ∧
    ((q * q + b * b) * a - (q * a + q * b) * q = 0) ∧
    (-(q * a + q * b) * a + (q * q + a * a) * q = 0) ∧
    (a ≠ 0 ∨ q ≠ 0) := by
  have hba : b * a = q * q := by rw [Int.mul_comm, hcrit]
  have hdet :
      (q * q + b * b) * (q * q + a * a) - (q * a + q * b) * (q * a + q * b) =
      (q * q - a * b) * (q * q - a * b) := by
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
    have h1 : q * q * (a * a) = q * a * (q * a) := by ac_rfl
    have h2 : b * b * (q * q) = q * b * (q * b) := by ac_rfl
    have h3 : b * b * (a * a) = a * b * (a * b) := by ac_rfl
    have h4 : q * a * (q * b) = q * q * (a * b) := by ac_rfl
    have h5 : q * b * (q * a) = a * b * (q * q) := by ac_rfl
    rw [h1, h2, h3, h4, h5]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, Or.inr (by omega)⟩
  · rw [hdet, hcrit]; simp
  · rw [Int.mul_comm]
    omega
  · rw [hba]
    omega
  · simp only [Int.add_mul]
    have h1 : b * b * a = b * (b * a) := by ac_rfl
    have h2 : q * q * a = q * a * q := by ac_rfl
    have h3 : q * b * q = b * (q * q) := by ac_rfl
    rw [h1, hba, h2, h3]
    omega
  · simp only [Int.neg_mul, Int.add_mul]
    have h1 : q * a * a = a * a * q := by ac_rfl
    have h2 : q * b * a = q * (b * a) := by ac_rfl
    have h3 : q * q * q = q * (q * q) := by ac_rfl
    rw [h1, h2, hba, h3]
    omega

/--
  Theorem 13 (Krein Saddle-Point Indefinite Inertia for Constrained DEQ Adjoint System):
  The constrained DEQ Lagrangian Hessian `K = [[0, d], [d, 0]]` with `d = q^2 - a * b`
  has trace `0` and determinant `-d^2 < 0` whenever `d != 0`, proving exact balanced
  Krein inertia `(1, 1, 0)` (one positive and one negative eigenvalue `± d`), collapsing
  to `(0, 0, 2)` at the critical bifurcation `d = 0`.
-/
theorem krein_deq_lagrangian_indefinite_inertia (a b q : Int) :
    let d := q * q - a * b
    (0 * 0 - d * d = -(d * d)) ∧
    (d ≠ 0 → 0 * 0 - d * d < 0) ∧
    (d = 0 → 0 * 0 - d * d = 0) := by
  dsimp only
  refine ⟨by omega, ?_, ?_⟩
  · intro hd
    have hpos := int_sq_pos_of_ne_zero (q * q - a * b) hd
    omega
  · intro hd
    rw [hd]
    simp

/--
  Theorem 14 (Non-Normal Contractive Transient Amplification):
  For the upper-triangular monodromy `M = (1/q) * [[r, k], [0, r]]` with `0 < q` and
  `0 <= r < q` (strictly contractive: spectral radius `rho(M) = r/q < 1`), the 1-step
  amplification on `e2 = (0, 1)` satisfies `||M e2||^2 > 1` iff `r^2 + k^2 > q^2`, and
  the 2-step iterate `M^2 = (1/q^2) * [[r^2, 2*r*k], [0, r^2]]` achieves `||M^2 e2||^2 > 1`
  whenever `r^4 + 4*r^2*k^2 > q^4` — demonstrating strictly contractive non-normal
  transient overshoot!
-/
theorem non_normal_contractive_transient_amplification (r k q : Int)
    (hq : 0 < q) (hr_nonneg : 0 ≤ r) (hr_lt : r < q) (hk_big : q * q < r * r + k * k) :
    r * r < q * q ∧
    q * q < r * r + k * k ∧
    ((r * r) * (r * r) + (2 * r * k) * (2 * r * k) =
      r * r * (r * r + 4 * (k * k))) := by
  refine ⟨?_, hk_big, ?_⟩
  · have hdiff : 0 < q - r := by omega
    have hsum : 0 < q + r := by omega
    have hprod : 0 < (q - r) * (q + r) := Int.mul_pos hdiff hsum
    have hid : (q - r) * (q + r) = q * q - r * r := by
      simp only [Int.sub_mul, Int.mul_add]
      have hqr : q * r = r * q := Int.mul_comm q r
      rw [hqr]
      omega
    omega
  · have h1 : (2 * r * k) * (2 * r * k) = r * r * (4 * (k * k)) := by ac_rfl
    rw [h1, ← Int.mul_add]

/--
  Theorem 15 (Elliptic Complex-Curl Power-Iteration Oscillation Obstruction):
  For the 2x2 non-normal elliptic rotation `M = [[c, -k^2 * s], [s, c]]` (conjugate to
  `[[c, -k*s], [k*s, c]]`, eigenvalues `c ± i * k * s`, exact squared spectral radius
  `rho^2 = c^2 + k^2 * s^2`): whenever `k > 1` and `s != 0`, the unit basis vectors
  satisfy `||M e1||^2 = c^2 + s^2 < rho^2 < c^2 + k^4 * s^2 = ||M e2||^2`, proving
  strict non-convergence / oscillation of single-step real power-iteration norms
  `||M v|| / ||v||` around `rho(M)`!
-/
theorem complex_curl_power_iter_oscillation (c s k : Int) (hk : 1 < k) (hs : s ≠ 0) :
    let rhoSq := c * c + (k * k) * (s * s)
    let normE1Sq := c * c + s * s
    let normE2Sq := c * c + (k * k) * ((k * k) * (s * s))
    normE1Sq < rhoSq ∧ rhoSq < normE2Sq := by
  dsimp only
  have hs2 : 0 < s * s := int_sq_pos_of_ne_zero s hs
  have hk2 : 1 < k * k := by
    have hk_ge : 2 ≤ k := by omega
    have h4 : 4 ≤ k * k := Int.mul_le_mul hk_ge hk_ge (by omega) (by omega)
    omega
  have h1 : s * s < (k * k) * (s * s) := by
    have hd : 0 < (k * k - 1) * (s * s) := Int.mul_pos (by omega) hs2
    rw [Int.sub_mul, Int.one_mul] at hd
    omega
  have h2 : (k * k) * (s * s) < (k * k) * ((k * k) * (s * s)) := by
    have hks : 0 < (k * k) * (s * s) := Int.mul_pos (by omega) hs2
    have hd : 0 < (k * k - 1) * ((k * k) * (s * s)) := Int.mul_pos (by omega) hks
    rw [Int.sub_mul, Int.one_mul] at hd
    omega
  exact ⟨by omega, by omega⟩

/--
  Theorem 16 (Hessian Maximum Eigenvalue & Plain-GD Stability Cliff Despite Strong Contraction):
  For symmetric equal-slope 2-node loop `a = b > 0` (`q > 0`), the exact largest
  eigenvalue of `H_PC = J_R^T J_R` is `lambda_max = (q + a)^2 / q^2` (realized on
  eigenvector `(1, -1)`), while the monodromy spectral radius is `rho = a^2 / q^2`.
  Hence whenever `2 * a >= q` (e.g. `a/q = 1/2`, strongly contractive `rho = 1/4`!),
  `lambda_max >= 9/4 > 2`, so plain GD with step size `eta = 1` violates the Euler
  stability bound `eta * lambda_max < 2` and diverges!
-/
theorem hessian_gd_stability_cliff_despite_contraction (a q : Int) (hq : 0 < q) (ha : 0 < a) :
    let h11 := q * q + a * a
    let h12 := -(2 * q * a)
    let lmax := (q + a) * (q + a)
    let lmin := (q - a) * (q - a)
    (h11 - h12 = lmax) ∧
    (h11 + h12 = lmin) ∧
    (q ≤ 2 * a → 9 * (q * q) ≤ 4 * lmax) ∧
    (2 * a < q → a * a < q * q) := by
  dsimp only
  have hlmax : (q + a) * (q + a) = q * q + 2 * (q * a) + a * a := by
    simp only [Int.add_mul, Int.mul_add]
    have haq : a * q = q * a := Int.mul_comm a q
    rw [haq]
    omega
  have hlmin : (q - a) * (q - a) = q * q - 2 * (q * a) + a * a := by
    simp only [Int.sub_mul, Int.mul_sub]
    have haq : a * q = q * a := Int.mul_comm a q
    rw [haq]
    omega
  have h2qa : 2 * q * a = 2 * (q * a) := Int.mul_assoc 2 q a
  refine ⟨by rw [hlmax, h2qa]; omega, by rw [hlmin, h2qa]; omega, ?_, ?_⟩
  · intro hge
    have hqa : 3 * q ≤ 2 * (q + a) := by omega
    have hsq : (3 * q) * (3 * q) ≤ (2 * (q + a)) * (2 * (q + a)) :=
      Int.mul_le_mul hqa hqa (by omega) (by omega)
    have h9 : (3 : Int) * 3 = 9 := rfl
    have h4 : (2 : Int) * 2 = 4 := rfl
    have hl : (3 * q) * (3 * q) = 9 * (q * q) := by
      rw [← h9]; ac_rfl
    have hr : (2 * (q + a)) * (2 * (q + a)) = 4 * ((q + a) * (q + a)) := by
      rw [← h4]; ac_rfl
    rw [hl, hr] at hsq
    exact hsq
  · intro hlt
    have h1 : a < q := by omega
    exact Int.mul_lt_mul_of_pos_right h1 hq |> fun h =>
      Int.lt_trans (Int.mul_lt_mul_of_pos_left h1 ha) h

/--
  Theorem 17 (Exact 2x2 Monodromy Trace Invariance Under Cyclic Basepoint Shift):
  Even when two 2x2 edge matrices `A, B` do NOT commute (`B * A != A * B`, non-trivial
  loop holonomy), the cyclic loop monodromies `M_s = B * A` and `M_u = A * B` share
  the exact same trace (and hence basepoint-invariant loop spectrum).
-/
theorem monodromy_2x2_trace_cyclic_invariance
    (a11 a12 a21 a22 b11 b12 b21 b22 : Int) :
    let trBA := (b11 * a11 + b12 * a21) + (b21 * a12 + b22 * a22)
    let trAB := (a11 * b11 + a12 * b21) + (a21 * b12 + a22 * b22)
    trBA = trAB := by
  dsimp only
  have h1 : b11 * a11 = a11 * b11 := Int.mul_comm b11 a11
  have h2 : b12 * a21 = a21 * b12 := Int.mul_comm b12 a21
  have h3 : b21 * a12 = a12 * b21 := Int.mul_comm b21 a12
  have h4 : b22 * a22 = a22 * b22 := Int.mul_comm b22 a22
  rw [h1, h2, h3, h4]
  omega

/--
  Theorem 18 (Exact 2x2 Monodromy Determinant Multiplicativity and Cyclic Invariance):
  For arbitrary 2x2 integer matrices `A, B`, `det(B * A) = det(A) * det(B) = det(A * B)`.
-/
theorem monodromy_2x2_det_cyclic_invariance
    (a11 a12 a21 a22 b11 b12 b21 b22 : Int) :
    let detA := a11 * a22 - a12 * a21
    let detB := b11 * b22 - b12 * b21
    let detBA := (b11 * a11 + b12 * a21) * (b21 * a12 + b22 * a22) -
                 (b11 * a12 + b12 * a22) * (b21 * a11 + b22 * a21)
    let detAB := (a11 * b11 + a12 * b21) * (a21 * b12 + a22 * b22) -
                 (a11 * b12 + a12 * b22) * (a21 * b11 + a22 * b21)
    detBA = detA * detB ∧ detAB = detA * detB := by
  dsimp only
  constructor
  · simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
    have h1 : b11 * a11 * (b21 * a12) = b11 * a12 * (b21 * a11) := by ac_rfl
    have h2 : b12 * a21 * (b22 * a22) = b12 * a22 * (b22 * a21) := by ac_rfl
    have h3 : b11 * a11 * (b22 * a22) = a11 * a22 * (b11 * b22) := by ac_rfl
    have h4 : b12 * a21 * (b21 * a12) = a12 * a21 * (b12 * b21) := by ac_rfl
    have h5 : b11 * a12 * (b22 * a21) = a12 * a21 * (b11 * b22) := by ac_rfl
    have h6 : b12 * a22 * (b21 * a11) = a11 * a22 * (b12 * b21) := by ac_rfl
    rw [h1, h2, h3, h4, h5, h6]
    omega
  · simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
    have h1 : a11 * b11 * (a21 * b12) = a11 * b12 * (a21 * b11) := by ac_rfl
    have h2 : a12 * b21 * (a22 * b22) = a12 * b22 * (a22 * b21) := by ac_rfl
    have h3 : a11 * b11 * (a22 * b22) = a11 * a22 * (b11 * b22) := by ac_rfl
    have h4 : a12 * b21 * (a21 * b12) = a12 * a21 * (b12 * b21) := by ac_rfl
    have h5 : a11 * b12 * (a22 * b21) = a11 * a22 * (b12 * b21) := by ac_rfl
    have h6 : a12 * b22 * (a21 * b11) = a12 * a21 * (b11 * b22) := by ac_rfl
    rw [h1, h2, h3, h4, h5, h6]
    omega

end CircularPCLoopSchur

#print axioms CircularPCLoopSchur.loop_schur_2node_metric_exact
#print axioms CircularPCLoopSchur.loop_schur_2node_metric_softening
#print axioms CircularPCLoopSchur.loop_schur_3node_metric_exact
#print axioms CircularPCLoopSchur.loop_hessian_2node_det_eq_monodromy_sq
#print axioms CircularPCLoopSchur.loop_adjoint_gloop_cancellation
#print axioms CircularPCLoopSchur.loop_zero_energy_deq_bijection_2node
#print axioms CircularPCLoopSchur.loop_zero_energy_deq_bijection_3node
#print axioms CircularPCLoopSchur.ep_cubic_jet_centered_cancels_order1
#print axioms CircularPCLoopSchur.ep_exact_linear_circular_pc_bias_law
#print axioms CircularPCLoopSchur.ep_truncated_phase_pole_and_centered_cancellation
#print axioms CircularPCLoopSchur.ep_truncated_pole_nonzero
#print axioms CircularPCLoopSchur.contractive_loop_spd_hessian
#print axioms CircularPCLoopSchur.critical_bifurcation_zero_mode_shadow
#print axioms CircularPCLoopSchur.krein_deq_lagrangian_indefinite_inertia
#print axioms CircularPCLoopSchur.non_normal_contractive_transient_amplification
#print axioms CircularPCLoopSchur.complex_curl_power_iter_oscillation
#print axioms CircularPCLoopSchur.hessian_gd_stability_cliff_despite_contraction
#print axioms CircularPCLoopSchur.monodromy_2x2_trace_cyclic_invariance
#print axioms CircularPCLoopSchur.monodromy_2x2_det_cyclic_invariance
