/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A172164
import Math0.Audit

/-!
# A172164: the second differences of the turns of the spiral of Theodorus are 18, 19, 20, 21

We prove Dumortier's conjecture: every term `a n` (`n ≥ 2`) lies in `{18, 19, 20, 21}`.

**Two one-step inequalities.** With `p = √k`, `q = √(k+1)`:
`arctan (1/q) ≤ 1/q ≤ 2(q - p)` (since `2pq ≤ p² + q²`), so `E k = S k - 2√k` is antitone; and for
`k ≥ 1`, `arctan (1/q) ≥ 1/q - 1/(3q³) ≥ 2(q - p) + 2/q - 2/p`, so `E k - 2/√k` is monotone.
Hence on a window `K₀ ≤ k`: `E k ≤ e := E K₀`, and up to `K₂`: `E k ≥ e - V`, `V = 2/√K₀ - 2/√K₂`.

**Counting.** For a threshold `θ` let `K` be the last index with `S K ≤ θ` and `L` the first with
`θ ≤ S L` (`L = K` if `S K = θ`, else `L = K + 1`). The complete triangles of turn `m` are
`L_{m-1} + 1, …, K_m`, so `a n = (K_n - L_{n-1}) - (K_{n-1} - L_{n-2})`.

**Squeeze.** With `T_i = 2π(n-2+i) - e` the window bounds give `2√K_i ≤ T_i + V`,
`2√(K_i+1) > T_i`, and `2√K_i ≥ T_i` when `S K_i` hits the threshold. Squaring and using
`T₂² + T₀² - 2T₁² = 8π²` gives `|a n - 2π²| < 2 + V T₁ + V²/2`, and for `n ≥ 71` (where
`√K₀ ≥ 200`) the error `V T₁ + V²/2 ≤ 0.13`, while `2π² ≈ 19.74`. So `17 < a n < 22`.
The terms `n ≤ 70` are the kernel-checked data `a_data` of the statement file.
-/

namespace Math0.Frontier.A172164
open Math0.Statements.A172164
open Real Finset

/-- One triangle angle is at most the increment of `2√k`: `arctan (1/√(k+1)) ≤ 2(√(k+1) - √k)`,
from `arctan x ≤ x` and `2√k √(k+1) ≤ 2k + 1`. -/
private theorem step_upper (k : ℕ) :
    arctan (1 / √((k : ℝ) + 1)) ≤ 2 * (√((k : ℝ) + 1) - √(k : ℝ)) := by
  have hq : 0 < √((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hp : 0 ≤ √(k : ℝ) := Real.sqrt_nonneg _
  have hq2 : √((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hp2 : √(k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
  set q := √((k : ℝ) + 1)
  set p := √(k : ℝ)
  have hq1 : 1 ≤ q := by
    rw [Real.one_le_sqrt]; have : (0 : ℝ) ≤ k := by positivity
    linarith
  have h1 : arctan (1 / q) ≤ 1 / q := by
    rcases eq_or_lt_of_le hq1 with h | h
    · rw [← h, div_one, Real.arctan_one]
      have := Real.pi_lt_d2
      linarith
    · have h' : 1 / q < 1 := by rw [div_lt_one hq]; exact h
      have := (arctan_alt_bounds (x := 1 / q) (by positivity) h' 0).2
      simpa using this
  have h2 : 1 / q ≤ 2 * (q - p) := by
    rw [div_le_iff₀ hq]
    nlinarith [sq_nonneg (q - p)]
  linarith

/-- For `k ≥ 1`, `arctan (1/√(k+1)) ≥ 2(√(k+1) - √k) + 2/√(k+1) - 2/√k`, from
`arctan x ≥ x - x³/3` and an algebraic identity in `p = √k`, `q = √(k+1)`. -/
private theorem step_lower (k : ℕ) (hk : 1 ≤ k) :
    2 * (√((k : ℝ) + 1) - √(k : ℝ)) + 2 / √((k : ℝ) + 1) - 2 / √(k : ℝ) ≤
      arctan (1 / √((k : ℝ) + 1)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 0 < √((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hp : 0 < √(k : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hq2 : √((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hp2 : √(k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
  set q := √((k : ℝ) + 1)
  set p := √(k : ℝ)
  have hpq : p < q := by nlinarith
  have hx1 : 1 / q < 1 := by
    rw [div_lt_one hq]; nlinarith
  have h1 := (arctan_alt_bounds (x := 1 / q) (by positivity) hx1 1).1
  simp [Finset.sum_range_succ] at h1
  have hN : 0 < 6 * q ^ 3 - 3 * p * q ^ 2 - p - 6 * p * q ^ 3 * (q - p) := by
    have e : (6 * q ^ 3 - 3 * p * q ^ 2 - p - 6 * p * q ^ 3 * (q - p)) * (q + p) =
        3 * q ^ 3 * (q - p) + q * (2 * q - p) + 1 := by
      have : p ^ 2 = q ^ 2 - 1 := by rw [hp2, hq2]; ring
      linear_combination (6 * p * q ^ 3 - 3 * q ^ 2 - 1) * this
    have h3 : 0 < 3 * q ^ 3 * (q - p) + q * (2 * q - p) + 1 := by
      have : 0 < q - p := by linarith
      have : 0 < 2 * q - p := by linarith
      positivity
    rw [← e] at h3
    exact pos_of_mul_pos_left h3 (by linarith)
  have key : 2 * (q - p) + 2 / q - 2 / p ≤ q⁻¹ - (q⁻¹) ^ 3 / 3 := by
    have e : q⁻¹ - (q⁻¹) ^ 3 / 3 - (2 * (q - p) + 2 / q - 2 / p) =
        (6 * q ^ 3 - 3 * p * q ^ 2 - p - 6 * p * q ^ 3 * (q - p)) / (3 * p * q ^ 3) := by
      field_simp; ring
    have : 0 ≤ (6 * q ^ 3 - 3 * p * q ^ 2 - p - 6 * p * q ^ 3 * (q - p)) / (3 * p * q ^ 3) := by
      positivity
    linarith
  rw [one_div]
  have h4 : (q ^ 3)⁻¹ / (2 + 1) = q⁻¹ ^ 3 / 3 := by rw [inv_pow]; norm_num
  linarith

/-- `S k - 2√k` is antitone. -/
private theorem E_anti (k m : ℕ) (h : k ≤ m) : S m - 2 * √(m : ℝ) ≤ S k - 2 * √(k : ℝ) := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    rw [S_succ]
    have := step_upper m
    push_cast
    linarith

/-- `S k - 2√k - 2/√k` is monotone on `k ≥ 1`. -/
private theorem E_mono (k m : ℕ) (hk : 1 ≤ k) (h : k ≤ m) :
    S k - 2 * √(k : ℝ) - 2 / √(k : ℝ) ≤ S m - 2 * √(m : ℝ) - 2 / √(m : ℝ) := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    rw [S_succ]
    have := step_lower m (by omega)
    push_cast
    linarith

/-- `S` is unbounded. -/
private theorem S_unbounded (θ : ℝ) : ∃ k, θ < S k := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((2 * |θ| + 2) ^ 2)
  refine ⟨N + 2, ?_⟩
  have h1 := S_ge (N + 2) (by omega)
  have h2 : 2 * |θ| + 2 ≤ √((N + 2 : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    push_cast
    linarith
  have h3 := le_abs_self θ
  nlinarith [abs_nonneg θ]

/-- One triangle adds less than `π/2`. -/
private theorem S_lt_succ_of_le {K : ℕ} {θ : ℝ} (h : S K ≤ θ) : S (K + 1) < θ + π / 2 := by
  rw [S_succ]
  have := arctan_lt_pi_div_two (1 / √((K : ℝ) + 1))
  linarith

/-- Monotonicity of `S`, in the form used for the indices. -/
private theorem le_of_S_lt {a b : ℕ} (h : S a < S (b + 1)) : a ≤ b := by
  by_contra hc
  have := S_strictMono.monotone (show b + 1 ≤ a by omega)
  linarith

/-- For `θ ≥ 0`: `K` is the largest index with `S K ≤ θ`, and `L` the least index with
`θ ≤ S L`; `L = K` exactly when `S K = θ`, otherwise `L = K + 1`. -/
private theorem exists_KL (θ : ℝ) (hθ : 0 ≤ θ) : ∃ K L : ℕ, S K ≤ θ ∧ θ < S (K + 1) ∧
    (∀ j, θ ≤ S j ↔ L ≤ j) ∧ ((L = K ∧ S K = θ) ∨ L = K + 1) := by
  classical
  have hex := S_unbounded θ
  have hk : θ < S (Nat.find hex) := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h; rw [h, S_zero] at hk; linarith
  obtain ⟨K, hK⟩ : ∃ K, Nat.find hex = K + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hKle : S K ≤ θ := by
    by_contra h; rw [not_le] at h
    exact Nat.find_min hex (show K < Nat.find hex by omega) h
  rw [hK] at hk
  rcases eq_or_lt_of_le hKle with heq | hlt
  · refine ⟨K, K, hKle, hk, fun j => ⟨fun hj => ?_, fun hj => ?_⟩, Or.inl ⟨rfl, heq⟩⟩
    · by_contra hc; rw [not_le] at hc
      have := S_strictMono hc; linarith
    · have := S_strictMono.monotone hj; linarith
  · refine ⟨K, K + 1, hKle, hk, fun j => ⟨fun hj => ?_, fun hj => ?_⟩, Or.inr rfl⟩
    · by_contra hc; rw [not_le] at hc
      have := S_strictMono.monotone (show j ≤ K by omega); linarith
    · have := S_strictMono.monotone hj; linarith

/-- `c m = K - L`, where `K` is the last index with `S K ≤ 2πm` and `L` the first with
`2π(m-1) ≤ S L`: the complete triangles of turn `m` are `L+1, …, K`. -/
private theorem c_formula (m : ℕ) (x y : ℝ) (hx : (m : ℝ) = x) (hy : 2 * π * (x - 1) = y) (K L : ℕ)
    (hK1 : S K ≤ 2 * π * x) (hK2 : 2 * π * x < S (K + 1)) (hL : ∀ j, y ≤ S j ↔ L ≤ j)
    (hLK : L ≤ K) : (c m : ℤ) = K - L := by
  have hT : turnTriangles m = Set.Icc (L + 1) K := by
    ext i
    simp only [turnTriangles, Set.mem_ofPred_eq, Set.mem_Icc]
    rw [hx, hy, hL]
    have : S i ≤ 2 * π * x ↔ i ≤ K := by
      constructor
      · intro h; exact le_of_S_lt (lt_of_le_of_lt h hK2)
      · intro h; exact le_trans (S_strictMono.monotone h) hK1
    rw [this]
    omega
  rw [c, hT, ncard_Icc_nat]
  omega


/-- The error term `V T₁ + V²/2` is at most `0.13` once `P = √K₀ ≥ 200`. -/
private theorem bound_X (p P Q V T0 : ℝ) (hp0 : 0 < p) (hp : p < 3.1416) (hP : 200 ≤ P)
    (hPQ : P ≤ Q) (hV0 : 0 ≤ V) (hVP : V * P ^ 2 ≤ 2 * (Q - P)) (hV : V ≤ 1 / 100)
    (hT0a : 2 * P ≤ T0) (hT0b : T0 < 2 * P + 1 / P) (hQb : 2 * Q ≤ T0 + 4 * p + V) :
    V * (T0 + 2 * p) + V ^ 2 / 2 ≤ 13 / 100 := by
  have hP0 : 0 < P := by linarith
  have hinvP : 1 / P ≤ 1 / 200 := one_div_le_one_div_of_le (by norm_num) hP
  have hT1pos : 0 < T0 + 2 * p := by linarith
  have hQP : Q - P ≤ 2 * p + 3 / 400 := by linarith
  have hQP0 : 0 ≤ Q - P := by linarith
  have hT1b : T0 + 2 * p ≤ 2 * P + 2 * p + 1 / 200 := by linarith
  have k1 : V * (T0 + 2 * p) * P ^ 2 ≤ 2 * (2 * p + 3 / 400) * (2 * P + 2 * p + 1 / 200) := by
    have h1 := mul_le_mul_of_nonneg_right hVP hT1pos.le
    have h2 : 2 * (Q - P) * (T0 + 2 * p) ≤ 2 * (2 * p + 3 / 400) * (2 * P + 2 * p + 1 / 200) := by
      have := mul_le_mul hQP hT1b hT1pos.le (by linarith)
      linarith
    have e : V * (T0 + 2 * p) * P ^ 2 = V * P ^ 2 * (T0 + 2 * p) := by ring
    linarith
  have k2 : 2 * (2 * p + 3 / 400) * (2 * P + 2 * p + 1 / 200) ≤
      2 * (6291 / 1000) * (2 * P + 6291 / 1000) := by
    have := mul_le_mul (show 2 * p + 3 / 400 ≤ 6291 / 1000 by linarith)
      (show 2 * P + 2 * p + 1 / 200 ≤ 2 * P + 6291 / 1000 by linarith) (by linarith) (by norm_num)
    linarith
  have k3 : 2 * (6291 / 1000 : ℝ) * (2 * P + 6291 / 1000) ≤ 129 / 1000 * P ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hP) hP0.le]
  have k4 : V * (T0 + 2 * p) ≤ 129 / 1000 := by
    have hP20 : 0 < P ^ 2 := by positivity
    have : V * (T0 + 2 * p) * P ^ 2 ≤ 129 / 1000 * P ^ 2 := by linarith
    exact le_of_mul_le_mul_right this hP20
  have k5 : V ^ 2 / 2 ≤ 1 / 1000 := by nlinarith
  linarith

/-- The final squeeze: `2π² - 2 - X < a < 2π² + 2 + X` with `X ≤ 0.13`. -/
private theorem final_bound (p T0 V A K1 K2 L0 L1 : ℝ) (hp1 : 3.14 < p) (hp2 : p < 3.1416)
    (hA : A = K2 - L1 - (K1 - L0))
    (hX : V * (T0 + 2 * p) + V ^ 2 / 2 ≤ 13 / 100)
    (F1 : 4 * K2 ≤ (T0 + 4 * p + V) ^ 2) (F2 : (T0 + 4 * p) ^ 2 < 4 * (K2 + 1))
    (F3 : 4 * L0 ≤ (T0 + V) ^ 2 + 4) (F4 : T0 ^ 2 ≤ 4 * L0)
    (F5 : (T0 + 2 * p) ^ 2 - 2 < 2 * (K1 + L1)) (F6 : 2 * (K1 + L1) ≤ (T0 + 2 * p + V) ^ 2 + 2) :
    17 < A ∧ A < 22 := by
  have I1 : (T0 + 4 * p + V) ^ 2 + (T0 + V) ^ 2 - 2 * (T0 + 2 * p) ^ 2 =
      8 * p ^ 2 + 4 * (V * (T0 + 2 * p)) + 2 * V ^ 2 := by ring
  have I2 : (T0 + 4 * p) ^ 2 + T0 ^ 2 - 2 * (T0 + 2 * p + V) ^ 2 =
      8 * p ^ 2 - 4 * (V * (T0 + 2 * p)) - 2 * V ^ 2 := by ring
  have hp3 : p ^ 2 < 987 / 100 := by nlinarith
  have hp4 : 985 / 100 < p ^ 2 := by nlinarith
  constructor <;> linarith


/-- `(2√x)² = 4x`. -/
private theorem two_sqrt_sq (x : ℝ) (hx : 0 ≤ x) : (2 * √x) ^ 2 = 4 * x := by
  rw [mul_pow, Real.sq_sqrt hx]; ring

/-- The analytic core: for three consecutive turns with `r0 ≥ 69`, the second difference lies
strictly between `17` and `22`. -/
private theorem core (r0 : ℝ) (hr : 69 ≤ r0) (K0 K1 K2 L0 L1 : ℕ)
    (h0a : S K0 ≤ 2 * π * r0) (h0b : 2 * π * r0 < S (K0 + 1))
    (h1a : S K1 ≤ 2 * π * (r0 + 1)) (h1b : 2 * π * (r0 + 1) < S (K1 + 1))
    (h2a : S K2 ≤ 2 * π * (r0 + 2)) (h2b : 2 * π * (r0 + 2) < S (K2 + 1))
    (hL0 : (L0 = K0 ∧ S K0 = 2 * π * r0) ∨ L0 = K0 + 1)
    (hL1 : (L1 = K1 ∧ S K1 = 2 * π * (r0 + 1)) ∨ L1 = K1 + 1) :
    17 < ((K2 : ℤ) - L1) - ((K1 : ℤ) - L0) ∧ ((K2 : ℤ) - L1) - ((K1 : ℤ) - L0) < 22 := by
  have hpi := Real.pi_pos
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d4
  have hK01 : K0 ≤ K1 := le_of_S_lt (by linarith)
  have hK12 : K1 ≤ K2 := le_of_S_lt (by linarith)
  set e := S K0 - 2 * √(K0 : ℝ) with he_def
  have he : e ≤ 0 := by
    have := E_anti 0 K0 (Nat.zero_le _)
    simp only [S_zero, Nat.cast_zero, Real.sqrt_zero] at this
    linarith
  -- upper bounds on `S - 2√·` beyond `K0`
  have hb : ∀ (K : ℕ) (θ : ℝ), K0 ≤ K → θ < S (K + 1) → θ - e < 2 * √((K : ℝ) + 1) := by
    intro K θ hK hθ
    have := E_anti K0 (K + 1) (by omega)
    push_cast at this
    linarith
  have hc : ∀ (K : ℕ) (θ : ℝ), K0 ≤ K → S K = θ → θ - e ≤ 2 * √(K : ℝ) := by
    intro K θ hK hθ
    have := E_anti K0 K hK
    linarith
  -- `K0` is large
  have hb0 := hb K0 _ le_rfl h0b
  have hK0big : (40000 : ℝ) ≤ K0 := by
    have hm : 3.14 * 69 ≤ π * r0 := mul_le_mul hpi1.le hr (by norm_num) hpi.le
    have h1 : (216 : ℝ) < √((K0 : ℝ) + 1) := by linarith
    rw [Real.lt_sqrt (by norm_num)] at h1
    linarith
  have hK0pos : 1 ≤ K0 := by
    have : (1 : ℝ) ≤ K0 := by linarith
    exact_mod_cast this
  have hP : (200 : ℝ) ≤ √(K0 : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
  have hP2 : √(K0 : ℝ) ^ 2 = K0 := Real.sq_sqrt (by positivity)
  have hPQ : √(K0 : ℝ) ≤ √(K2 : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hK01.trans hK12)
  set P := √(K0 : ℝ) with hP_def
  set Q := √(K2 : ℝ) with hQ_def
  set V := 2 / P - 2 / Q with hV_def
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hV0 : 0 ≤ V := by
    rw [hV_def, sub_nonneg]
    exact div_le_div_of_nonneg_left (by norm_num) hP0 hPQ
  have hVP : V * P ^ 2 ≤ 2 * (Q - P) := by
    have e1 : V * P * Q = 2 * (Q - P) := by
      rw [hV_def]; field_simp
    have := mul_le_mul_of_nonneg_left hPQ (mul_nonneg hV0 hP0.le)
    have e2 : V * P ^ 2 = V * P * P := by ring
    linarith
  have hVlt : V ≤ 2 / P := by
    rw [hV_def]; have : 0 < 2 / Q := by positivity
    linarith
  have hVsmall : V ≤ 1 / 100 := by
    calc V ≤ 2 / P := hVlt
      _ ≤ 2 / 200 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hP
      _ = 1 / 100 := by norm_num
  -- lower bounds on `S - 2√·` up to `K2`
  have ha : ∀ (K : ℕ) (θ : ℝ), K0 ≤ K → K ≤ K2 → S K ≤ θ → 2 * √(K : ℝ) ≤ θ - e + V := by
    intro K θ h1 h2 h3
    have := E_mono K0 K hK0pos h1
    have hs1 : P ≤ √(K : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast h1)
    have hs2 : √(K : ℝ) ≤ Q := Real.sqrt_le_sqrt (by exact_mod_cast h2)
    have : 2 / Q ≤ 2 / √(K : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by linarith) hs2
    rw [hV_def]
    linarith
  set T0 := 2 * π * r0 - e with hT0_def
  have hT0a : 2 * P ≤ T0 := by rw [hT0_def, he_def]; linarith
  have hsq1 : √((K0 : ℝ) + 1) ≤ P + 1 / (2 * P) := by
    rw [Real.sqrt_le_left (by positivity)]
    have h4 : 0 ≤ 1 / (4 * P ^ 2) := by positivity
    have : (P + 1 / (2 * P)) ^ 2 = P ^ 2 + 1 + 1 / (4 * P ^ 2) := by field_simp; ring
    rw [this]
    linarith
  have hT0b : T0 < 2 * P + 1 / P := by
    have : 2 * (1 / (2 * P)) = 1 / P := by field_simp
    linarith
  have hQb : 2 * Q ≤ T0 + 4 * π + V := by
    have := ha K2 _ (hK01.trans hK12) le_rfl h2a
    rw [hT0_def]; linarith
  have hX := bound_X π P Q V T0 hpi hpi2 hP hPQ hV0 hVP hVsmall hT0a hT0b hQb
  -- the six facts
  have hK0r : (0 : ℝ) ≤ K0 := by positivity
  have hK1r : (0 : ℝ) ≤ K1 := by positivity
  have hK2r : (0 : ℝ) ≤ K2 := by positivity
  have F1 : 4 * (K2 : ℝ) ≤ (T0 + 4 * π + V) ^ 2 := by
    rw [← two_sqrt_sq _ hK2r]
    exact pow_le_pow_left₀ (by positivity) hQb 2
  have F2 : (T0 + 4 * π) ^ 2 < 4 * ((K2 : ℝ) + 1) := by
    have := hb K2 _ (hK01.trans hK12) h2b
    have h' : T0 + 4 * π < 2 * √((K2 : ℝ) + 1) := by linarith
    rw [← two_sqrt_sq ((K2 : ℝ) + 1) (by positivity)]
    exact pow_lt_pow_left₀ h' (by linarith) two_ne_zero
  have G0 : T0 ^ 2 < 4 * ((K0 : ℝ) + 1) := by
    rw [← two_sqrt_sq _ (by positivity)]
    exact pow_lt_pow_left₀ hb0 (by linarith) two_ne_zero
  have G0' : 4 * (K0 : ℝ) ≤ T0 ^ 2 := by
    rw [← two_sqrt_sq _ hK0r]
    exact pow_le_pow_left₀ (by positivity) hT0a 2
  have F3 : 4 * (L0 : ℝ) ≤ (T0 + V) ^ 2 + 4 := by
    have hL : (L0 : ℝ) ≤ K0 + 1 := by
      rcases hL0 with ⟨h, -⟩ | h <;> subst h <;> push_cast <;> linarith
    have : T0 ^ 2 ≤ (T0 + V) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    linarith
  have F4 : T0 ^ 2 ≤ 4 * (L0 : ℝ) := by
    rcases hL0 with ⟨h, h'⟩ | h
    · rw [h]
      have := hc K0 _ le_rfl h'
      rw [← two_sqrt_sq _ hK0r]
      exact pow_le_pow_left₀ (by linarith) this 2
    · subst h; push_cast; linarith
  have G1 : (T0 + 2 * π) ^ 2 < 4 * ((K1 : ℝ) + 1) := by
    have := hb K1 _ hK01 h1b
    have h' : T0 + 2 * π < 2 * √((K1 : ℝ) + 1) := by linarith
    rw [← two_sqrt_sq _ (by positivity)]
    exact pow_lt_pow_left₀ h' (by linarith) two_ne_zero
  have G1' : 4 * (K1 : ℝ) ≤ (T0 + 2 * π + V) ^ 2 := by
    have := ha K1 _ hK01 hK12 h1a
    have h' : 2 * √(K1 : ℝ) ≤ T0 + 2 * π + V := by linarith
    rw [← two_sqrt_sq _ hK1r]
    exact pow_le_pow_left₀ (by positivity) h' 2
  have F5 : (T0 + 2 * π) ^ 2 - 2 < 2 * ((K1 : ℝ) + L1) := by
    rcases hL1 with ⟨h, h'⟩ | h
    · rw [h]
      have := hc K1 _ hK01 h'
      have h'' : T0 + 2 * π ≤ 2 * √(K1 : ℝ) := by linarith
      have : (T0 + 2 * π) ^ 2 ≤ 4 * (K1 : ℝ) := by
        rw [← two_sqrt_sq _ hK1r]
        exact pow_le_pow_left₀ (by linarith) h'' 2
      linarith
    · subst h; push_cast; linarith
  have F6 : 2 * ((K1 : ℝ) + L1) ≤ (T0 + 2 * π + V) ^ 2 + 2 := by
    have hL : (L1 : ℝ) ≤ K1 + 1 := by
      rcases hL1 with ⟨h, -⟩ | h <;> subst h <;> push_cast <;> linarith
    linarith
  obtain ⟨r1, r2⟩ := final_bound π T0 V (((K2 : ℤ) - L1) - ((K1 : ℤ) - L0) : ℤ) K1 K2 L0 L1
    hpi1 hpi2 (by push_cast; ring) hX F1 F2 F3 F4 F5 F6
  constructor
  · exact_mod_cast r1
  · exact_mod_cast r2

/-- Dumortier's conjecture for A172164: every term `a n` (`n ≥ 2`) is `18`, `19`, `20` or `21`. -/
theorem result : statement := by
  intro n hn
  rcases le_or_gt n 70 with h70 | h70
  · have hmem : a n ∈ (List.range 69).map (fun i => a (i + 2)) :=
      List.mem_map.2 ⟨n - 2, List.mem_range.2 (by omega), by rw [show n - 2 + 2 = n by omega]⟩
    have hall : ∀ x ∈ (List.range 69).map (fun i => a (i + 2)),
        x = 18 ∨ x = 19 ∨ x = 20 ∨ x = 21 := by
      rw [a_data]; decide
    exact hall _ hmem
  · obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, r0 = (n : ℝ) - 2 := ⟨_, rfl⟩
    have hn71 : (71 : ℝ) ≤ n := by exact_mod_cast h70
    have hr : 69 ≤ r0 := by rw [hr0]; linarith
    have hpi := Real.pi_pos
    obtain ⟨K0, L0, h0a, h0b, hL0, hL0'⟩ := exists_KL (2 * π * r0) (by positivity)
    obtain ⟨K1, L1, h1a, h1b, hL1, hL1'⟩ := exists_KL (2 * π * (r0 + 1)) (by positivity)
    obtain ⟨K2, L2, h2a, h2b, -, -⟩ := exists_KL (2 * π * (r0 + 2)) (by positivity)
    have hL0K1 : L0 ≤ K1 := by
      have h1 : L0 ≤ K0 + 1 := by rcases hL0' with ⟨h, -⟩ | h <;> omega
      have h2 : K0 + 1 ≤ K1 := le_of_S_lt (by have := S_lt_succ_of_le h0a; linarith)
      omega
    have hL1K2 : L1 ≤ K2 := by
      have h1 : L1 ≤ K1 + 1 := by rcases hL1' with ⟨h, -⟩ | h <;> omega
      have h2 : K1 + 1 ≤ K2 := le_of_S_lt (by have := S_lt_succ_of_le h1a; linarith)
      omega
    have hcn : (c n : ℤ) = K2 - L1 :=
      c_formula n (r0 + 2) (2 * π * (r0 + 1)) (by rw [hr0]; ring) (by ring) K2 L1 h2a h2b hL1 hL1K2
    have hcn1 : (c (n - 1) : ℤ) = K1 - L0 :=
      c_formula (n - 1) (r0 + 1) (2 * π * r0)
        (by rw [Nat.cast_sub (by omega), hr0]; push_cast; ring)
        (by ring) K1 L0 h1a h1b hL0 hL0K1
    obtain ⟨l, u⟩ := core r0 hr K0 K1 K2 L0 L1 h0a h0b h1a h1b h2a h2b hL0' hL1'
    have ha : a n = ((K2 : ℤ) - L1) - ((K1 : ℤ) - L0) := by rw [a, hcn, hcn1]
    omega

end Math0.Frontier.A172164

#math0_settles Math0.Frontier.A172164.result Math0.Statements.A172164.statement
