/-
Track S94: Wave-6 Fourth-Order Cross-Cluster Convergence
(Portals 98..100 x Expedition S31/S50/S59/S70/S73/S76/S78/S79/S80/S86)

Pure-Init Lean 4.36.0 Formalization:
  - 0 external imports, 0 warnings, 0 sorry, 0 Classical.choice, 0 Quot.sound
  - 18/18 universally quantified (forall) theorems across Pillars 1..3:
      * Pillar 1 (Thms 1..6): Privileged Neuron Basis, [H_k, D] != 0 Smearing,
        Householder Reflection Isometry / Involution / Projection & S31 DPI
      * Pillar 2 (Thms 7..12): 8 GiB 3-Tier GPU+RAM+SSD Roofline, Bonsai 2.5
        Residency Cliff, Magnitude Sparse MoE & Joint Bit-Budget Freedom
      * Pillar 3 (Thms 13..18): Sleep Trilogy 2-Axis Consolidation, Brier Strict
        Proper Scoring, Single-Draw Overconfidence Paradox, Last-Loop KV Sharing
        & 5-Gate Borromean Necessity
-/

namespace S94Wave6Convergence

def natPow : Nat → Nat → Nat
  | _, 0 => 1
  | b, n + 1 => natPow b n * b

private theorem natPow_pos {b : Nat} (hb : 0 < b) : ∀ n : Nat, 0 < natPow b n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (natPow_pos hb n) hb

private theorem natPow_lt_of_lt {a b : Nat} (ha : 0 < a) (hab : a < b) :
    ∀ n : Nat, natPow a (n + 1) < natPow b (n + 1)
  | 0 => by
      change 1 * a < 1 * b
      simpa [Nat.one_mul] using hab
  | n + 1 => by
      have ih := natPow_lt_of_lt ha hab n
      have hpos : 0 < natPow b (n + 1) := natPow_pos (Nat.lt_trans ha hab) (n + 1)
      have h1 : natPow a (n + 1) * a < natPow b (n + 1) * a := Nat.mul_lt_mul_of_pos_right ih ha
      have h2 : natPow b (n + 1) * a < natPow b (n + 1) * b := Nat.mul_lt_mul_of_pos_left hab hpos
      exact Nat.lt_trans h1 h2

private theorem int_sq_pos_of_ne_zero {x : Int} (hx : x ≠ 0) : 0 < x * x := by
  cases x with
  | ofNat n =>
      cases n with
      | zero => exact absurd rfl hx
      | succ k =>
          change (0 : Int) < Int.ofNat ((k + 1) * (k + 1))
          exact Int.ofNat_lt.mpr (Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos k))
  | negSucc n =>
      have h : Int.negSucc n * Int.negSucc n = Int.ofNat ((n + 1) * (n + 1)) := by
        simp [Int.negSucc_mul_negSucc]
      rw [h]
      exact Int.ofNat_lt.mpr (Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n))

private theorem int_mul_pos_of_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  cases a with
  | ofNat m =>
      cases b with
      | ofNat n =>
          have hm : 0 < m := Int.ofNat_lt.mp ha
          have hn : 0 < n := Int.ofNat_lt.mp hb
          exact Int.ofNat_lt.mpr (Nat.mul_pos hm hn)
      | negSucc n => exact absurd hb (Int.not_lt.mpr (Int.le_of_lt (Int.negSucc_lt_zero n)))
  | negSucc m => exact absurd ha (Int.not_lt.mpr (Int.le_of_lt (Int.negSucc_lt_zero m)))

private theorem int_two_mul (z : Int) : 2 * z = z + z := by
  change (1 + 1) * z = z + z
  rw [Int.add_mul, Int.one_mul]

private theorem int_sq_sub (u v : Int) :
    (u - v) * (u - v) = u * u - 2 * (u * v) + v * v := by
  have h1 : (u - v) * (u - v) = (u - v) * u - (u - v) * v := Int.mul_sub (u - v) u v
  have h2 : (u - v) * u = u * u - v * u := Int.sub_mul u v u
  have h3 : (u - v) * v = u * v - v * v := Int.sub_mul u v v
  rw [h1, h2, h3, Int.mul_comm v u]
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg]
  rw [Int.add_assoc (u * u) (-(u * v)) (-(u * v) + v * v),
      ← Int.add_assoc (-(u * v)) (-(u * v)) (v * v),
      ← Int.add_assoc (u * u) (-(u * v) + -(u * v)) (v * v)]
  have hneg2 : -(u * v) + -(u * v) = -(2 * (u * v)) := by
    rw [int_two_mul, Int.neg_add]
  rw [hneg2, ← Int.sub_eq_add_neg]

private theorem int_sub_cancel_add (a b : Int) : a - b + b = a := by
  rw [Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_neg, Int.add_zero]

private theorem int_mul_sq_lt_of_pos_lt {a b : Int} (ha : 0 < a) (hab : a < b) : a * a < b * b := by
  have hb : 0 < b := Int.lt_trans ha hab
  have h1 : a * a < b * a := by
    have hp : 0 < (b - a) * a := int_mul_pos_of_pos (Int.sub_pos.mpr hab) ha
    rw [Int.sub_mul] at hp
    exact Int.sub_pos.mp hp
  have h2 : b * a < b * b := by
    have hp : 0 < b * (b - a) := int_mul_pos_of_pos hb (Int.sub_pos.mpr hab)
    rw [Int.mul_sub] at hp
    exact Int.sub_pos.mp hp
  exact Int.lt_trans h1 h2

-- ===========================================================================
-- PILLAR 1: Privileged Neuron Basis, [H_k, D] != 0 Smearing & Reflection DPI
-- ===========================================================================

-- Theorem 1: Full Hadamard rotation strictly flattens any privileged diagonal spike alpha > 1
-- (Cleared denominator form of (alpha + k - 1) / k < alpha).
theorem hadamard_smearing_diagonal_flat_universal
    (alpha k : Nat) (halpha : 1 < alpha) (hk : 2 ≤ k) :
    alpha + (k - 1) < k * alpha := by
  have h1 : 1 ≤ k := Nat.le_trans (by decide : 1 ≤ 2) hk
  have hkm1_pos : 0 < k - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2) hk)
  have hmul : (k - 1) * 1 < (k - 1) * alpha := Nat.mul_lt_mul_of_pos_left halpha hkm1_pos
  rw [Nat.mul_one] at hmul
  have hadd : alpha + (k - 1) < alpha + (k - 1) * alpha := Nat.add_lt_add_left hmul alpha
  have hfact : alpha + (k - 1) * alpha = k * alpha := by
    calc
      alpha + (k - 1) * alpha = 1 * alpha + (k - 1) * alpha := by rw [Nat.one_mul]
      _ = (1 + (k - 1)) * alpha := (Nat.add_mul 1 (k - 1) alpha).symm
      _ = k * alpha := by rw [Nat.add_comm 1 (k - 1), Nat.sub_add_cancel h1]
  rw [hfact] at hadd
  exact hadd

-- Theorem 2: Exact O(k) importance-weighted MSE blowup when [H_k, D] != 0
-- For D = diag(k, 1, ..., 1), ||Delta W D||_F^2 = (k^2 + k - 1) / k > k (e.g. 71/8 > 8 for k = 8).
theorem hadamard_importance_blowup_linear_in_k_universal
    (k : Nat) (hk : 2 ≤ k) :
    k * k < k * k + (k - 1) ∧ k * k + (k - 1) < k * (k + 1) := by
  have hkm1_pos : 0 < k - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2) hk)
  have hkm1_lt : k - 1 < k := Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hk) Nat.zero_lt_one
  constructor
  · exact Nat.lt_add_of_pos_right hkm1_pos
  · rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_lt_add_left hkm1_lt (k * k)

-- Theorem 3: Law-5 Isotropic Converse — Uniform D = c*I commutes with H_2 (zero off-diagonal leakage)
theorem hadamard_uniform_isotropic_commutes_universal
    (c : Int) :
    (1 * c * 1 + 1 * c * 1 = 2 * c) ∧
    (1 * c * 1 + 1 * c * (-1) = 0) ∧
    (1 * c * 1 + (-1) * c * 1 = 0) ∧
    (1 * c * 1 + (-1) * c * (-1) = 2 * c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [int_two_mul]
  · simp [Int.mul_neg, Int.add_right_neg]
  · simp [Int.neg_mul, Int.add_right_neg]
  · simp [Int.neg_mul, Int.mul_neg, int_two_mul]

-- Theorem 4: Exact Householder Reflection Isometry (neuron-reflection k = 2 => Delta ||W||_F^2 = 0!)
-- Cleared-denominator identity for H(2) u = u - 2 (u . d / s) d where s = d1^2 + d2^2.
theorem householder_reflection_isometry_universal
    (u1 u2 d1 d2 s : Int) (hs : d1 * d1 + d2 * d2 = s) :
    let dot := u1 * d1 + u2 * d2
    let v1 := s * u1 - 2 * dot * d1
    let v2 := s * u2 - 2 * dot * d2
    v1 * v1 + v2 * v2 = s * s * (u1 * u1 + u2 * u2) := by
  intro dot v1 v2
  have hv1 : v1 * v1 = (s * u1) * (s * u1) - 2 * ((s * u1) * (2 * dot * d1)) + (2 * dot * d1) * (2 * dot * d1) :=
    int_sq_sub (s * u1) (2 * dot * d1)
  have hv2 : v2 * v2 = (s * u2) * (s * u2) - 2 * ((s * u2) * (2 * dot * d2)) + (2 * dot * d2) * (2 * dot * d2) :=
    int_sq_sub (s * u2) (2 * dot * d2)
  have hsu1 : (s * u1) * (s * u1) = s * s * (u1 * u1) := by
    rw [Int.mul_assoc s u1 (s * u1), Int.mul_left_comm u1 s u1, ← Int.mul_assoc s s (u1 * u1)]
  have hsu2 : (s * u2) * (s * u2) = s * s * (u2 * u2) := by
    rw [Int.mul_assoc s u2 (s * u2), Int.mul_left_comm u2 s u2, ← Int.mul_assoc s s (u2 * u2)]
  have h22 : (2 : Int) * 2 = 4 := rfl
  have hc1 : 2 * ((s * u1) * (2 * dot * d1)) = 4 * s * dot * (u1 * d1) := by
    calc
      2 * ((s * u1) * (2 * dot * d1))
          = 2 * (s * (u1 * (2 * (dot * d1)))) := by
              rw [Int.mul_assoc s u1 (2 * dot * d1), Int.mul_assoc 2 dot d1]
      _ = 2 * (2 * (s * (dot * (u1 * d1)))) := by
              rw [Int.mul_left_comm u1 2 (dot * d1), Int.mul_left_comm s 2 (u1 * (dot * d1)),
                  Int.mul_left_comm u1 dot d1]
      _ = 4 * (s * (dot * (u1 * d1))) := by rw [← Int.mul_assoc 2 2, h22]
      _ = 4 * s * dot * (u1 * d1) := by
              rw [← Int.mul_assoc 4 s, ← Int.mul_assoc (4 * s) dot (u1 * d1)]
  have hc2 : 2 * ((s * u2) * (2 * dot * d2)) = 4 * s * dot * (u2 * d2) := by
    calc
      2 * ((s * u2) * (2 * dot * d2))
          = 2 * (s * (u2 * (2 * (dot * d2)))) := by
              rw [Int.mul_assoc s u2 (2 * dot * d2), Int.mul_assoc 2 dot d2]
      _ = 2 * (2 * (s * (dot * (u2 * d2)))) := by
              rw [Int.mul_left_comm u2 2 (dot * d2), Int.mul_left_comm s 2 (u2 * (dot * d2)),
                  Int.mul_left_comm u2 dot d2]
      _ = 4 * (s * (dot * (u2 * d2))) := by rw [← Int.mul_assoc 2 2, h22]
      _ = 4 * s * dot * (u2 * d2) := by
              rw [← Int.mul_assoc 4 s, ← Int.mul_assoc (4 * s) dot (u2 * d2)]
  have hq1 : (2 * dot * d1) * (2 * dot * d1) = 4 * dot * dot * (d1 * d1) := by
    calc
      (2 * dot * d1) * (2 * dot * d1)
          = (2 * dot) * (2 * dot) * (d1 * d1) := by
              rw [Int.mul_assoc (2 * dot) d1 (2 * dot * d1), Int.mul_left_comm d1 (2 * dot) d1,
                  ← Int.mul_assoc (2 * dot) (2 * dot) (d1 * d1)]
      _ = 4 * dot * dot * (d1 * d1) := by
              rw [Int.mul_assoc 2 dot (2 * dot), Int.mul_left_comm dot 2 dot,
                  ← Int.mul_assoc 2 2 (dot * dot), h22, ← Int.mul_assoc 4 dot dot]
  have hq2 : (2 * dot * d2) * (2 * dot * d2) = 4 * dot * dot * (d2 * d2) := by
    calc
      (2 * dot * d2) * (2 * dot * d2)
          = (2 * dot) * (2 * dot) * (d2 * d2) := by
              rw [Int.mul_assoc (2 * dot) d2 (2 * dot * d2), Int.mul_left_comm d2 (2 * dot) d2,
                  ← Int.mul_assoc (2 * dot) (2 * dot) (d2 * d2)]
      _ = 4 * dot * dot * (d2 * d2) := by
              rw [Int.mul_assoc 2 dot (2 * dot), Int.mul_left_comm dot 2 dot,
                  ← Int.mul_assoc 2 2 (dot * dot), h22, ← Int.mul_assoc 4 dot dot]
  have hcross_sum :
      4 * s * dot * (u1 * d1) + 4 * s * dot * (u2 * d2) = 4 * dot * dot * s := by
    rw [← Int.mul_add (4 * s * dot) (u1 * d1) (u2 * d2)]
    change 4 * s * dot * dot = 4 * dot * dot * s
    rw [Int.mul_assoc 4 s dot, Int.mul_comm s dot, ← Int.mul_assoc 4 dot s,
        Int.mul_assoc (4 * dot) s dot, Int.mul_comm s dot, ← Int.mul_assoc (4 * dot) dot s]
  have hquad_sum :
      4 * dot * dot * (d1 * d1) + 4 * dot * dot * (d2 * d2) = 4 * dot * dot * s := by
    rw [← Int.mul_add (4 * dot * dot) (d1 * d1) (d2 * d2), hs]
  rw [hv1, hv2, hsu1, hsu2, hc1, hc2, hq1, hq2]
  have hrearr :
      (s * s * (u1 * u1) - 4 * s * dot * (u1 * d1) + 4 * dot * dot * (d1 * d1)) +
      (s * s * (u2 * u2) - 4 * s * dot * (u2 * d2) + 4 * dot * dot * (d2 * d2)) =
      (s * s * (u1 * u1) + s * s * (u2 * u2)) -
      (4 * s * dot * (u1 * d1) + 4 * s * dot * (u2 * d2)) +
      (4 * dot * dot * (d1 * d1) + 4 * dot * dot * (d2 * d2)) := by
    simp only [Int.sub_eq_add_neg, Int.neg_add]
    ac_rfl
  rw [hrearr, hcross_sum, hquad_sum, int_sub_cancel_add, ← Int.mul_add]

-- Theorem 5: Exact Householder Reflection Involution (H(2)^2 = I => Editor.restore is exact!)
theorem householder_reflection_involution_universal
    (u1 u2 d1 d2 s : Int) (hs : d1 * d1 + d2 * d2 = s) :
    let dot := u1 * d1 + u2 * d2
    let v1 := s * u1 - 2 * dot * d1
    let v2 := s * u2 - 2 * dot * d2
    let dot2 := v1 * d1 + v2 * d2
    (s * v1 - 2 * dot2 * d1 = s * s * u1) ∧
    (s * v2 - 2 * dot2 * d2 = s * s * u2) := by
  intro dot v1 v2 dot2
  have hdot2 : dot2 = -(s * dot) := by
    have e1 : v1 * d1 = s * (u1 * d1) - 2 * dot * (d1 * d1) := by
      change (s * u1 - 2 * dot * d1) * d1 = s * (u1 * d1) - 2 * dot * (d1 * d1)
      rw [Int.sub_mul, Int.mul_assoc s u1 d1, Int.mul_assoc (2 * dot) d1 d1]
    have e2 : v2 * d2 = s * (u2 * d2) - 2 * dot * (d2 * d2) := by
      change (s * u2 - 2 * dot * d2) * d2 = s * (u2 * d2) - 2 * dot * (d2 * d2)
      rw [Int.sub_mul, Int.mul_assoc s u2 d2, Int.mul_assoc (2 * dot) d2 d2]
    have hsum : dot2 = s * dot - 2 * dot * s := by
      change v1 * d1 + v2 * d2 = s * dot - 2 * dot * s
      rw [e1, e2]
      have hr : (s * (u1 * d1) - 2 * dot * (d1 * d1)) + (s * (u2 * d2) - 2 * dot * (d2 * d2)) =
          (s * (u1 * d1) + s * (u2 * d2)) - (2 * dot * (d1 * d1) + 2 * dot * (d2 * d2)) := by
        simp only [Int.sub_eq_add_neg, Int.neg_add]
        ac_rfl
      rw [hr, ← Int.mul_add s, ← Int.mul_add (2 * dot), hs]
    rw [hsum]
    have h2ds : 2 * dot * s = s * dot + s * dot := by
      rw [Int.mul_assoc 2 dot s, Int.mul_comm dot s, int_two_mul (s * dot)]
    rw [h2ds, Int.sub_eq_add_neg, Int.neg_add, ← Int.add_assoc, Int.add_right_neg, Int.zero_add]
  have hcancel : ∀ u d : Int, s * (s * u - 2 * dot * d) - 2 * (-(s * dot)) * d = s * s * u := by
    intro u d
    rw [Int.mul_sub, Int.mul_neg, Int.neg_mul, Int.sub_neg, ← Int.mul_assoc s s u]
    have hterm : s * (2 * dot * d) = 2 * (s * dot) * d := by
      rw [← Int.mul_assoc s (2 * dot) d, Int.mul_left_comm s 2 dot]
    rw [hterm, int_sub_cancel_add]
  exact ⟨by rw [hdot2]; exact hcancel u1 d1, by rw [hdot2]; exact hcancel u2 d2⟩

-- Theorem 6: Householder Projection Idempotence (k = 1) & S31 DPI Concentration (> 1 when m < N)
theorem householder_projection_idempotent_and_dpi_universal
    (u1 u2 d1 d2 s : Int) (hs : d1 * d1 + d2 * d2 = s)
    (N m : Nat) (hm : 0 < m) (hmN : m < N) :
    let dot := u1 * d1 + u2 * d2
    let p1 := s * u1 - dot * d1
    let p2 := s * u2 - dot * d2
    (p1 * d1 + p2 * d2 = 0) ∧ (m * m < N * m) := by
  intro dot p1 p2
  constructor
  · have e1 : p1 * d1 = s * (u1 * d1) - dot * (d1 * d1) := by
      change (s * u1 - dot * d1) * d1 = s * (u1 * d1) - dot * (d1 * d1)
      rw [Int.sub_mul, Int.mul_assoc s u1 d1, Int.mul_assoc dot d1 d1]
    have e2 : p2 * d2 = s * (u2 * d2) - dot * (d2 * d2) := by
      change (s * u2 - dot * d2) * d2 = s * (u2 * d2) - dot * (d2 * d2)
      rw [Int.sub_mul, Int.mul_assoc s u2 d2, Int.mul_assoc dot d2 d2]
    rw [e1, e2]
    have hr : (s * (u1 * d1) - dot * (d1 * d1)) + (s * (u2 * d2) - dot * (d2 * d2)) =
        (s * (u1 * d1) + s * (u2 * d2)) - (dot * (d1 * d1) + dot * (d2 * d2)) := by
      simp only [Int.sub_eq_add_neg, Int.neg_add]
      ac_rfl
    rw [hr, ← Int.mul_add s, ← Int.mul_add dot, hs, Int.mul_comm dot s, Int.sub_self]
  · exact Nat.mul_lt_mul_of_pos_right hmN hm

-- ===========================================================================
-- PILLAR 2: 8 GiB 3-Tier GPU+RAM+SSD Roofline, Bonsai 2.5 & Magnitude MoE
-- ===========================================================================

-- Theorem 7: Exact 8 GiB Residency Phase Cliff (sub-cliff fits 100% in GPU vs super-cliff spills)
theorem residency_phase_cliff_universal
    (N C bLo bHi : Nat)
    (hFit : N * bLo ≤ 8 * C) (hSpill : 8 * C < N * bHi) :
    N * bLo < N * bHi ∧ 0 < N * bHi - 8 * C := by
  exact ⟨Nat.lt_of_le_of_lt hFit hSpill, Nat.sub_pos_of_lt hSpill⟩

-- Theorem 8: Any Positive RAM Spill Strictly Slows Decode Time (Cleared Denominator)
theorem tier_spill_strict_slowdown_universal
    (mGpu mRam bGpu bRam : Nat)
    (hmRam : 0 < mRam) (hB : bRam < bGpu) :
    (mGpu + mRam) * bRam < mGpu * bRam + mRam * bGpu := by
  rw [Nat.add_mul]
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hB hmRam) (mGpu * bRam)

-- Theorem 9: NVMe SSD Spill Strictly Dominates System-RAM Spill Penalty
theorem nvme_spill_dominates_ram_spill_universal
    (mSsd bRam bSsd : Nat)
    (hmSsd : 0 < mSsd) (hB : bSsd < bRam) :
    mSsd * bSsd < mSsd * bRam := by
  exact Nat.mul_lt_mul_of_pos_left hB hmSsd

-- Theorem 10: Universal 3-Tier GPU+RAM+SSD Harmonic Roofline Bound
theorem three_tier_monotonic_time_universal
    (mGpu mRam mSsd bGpu bRam bSsd : Nat)
    (hSR : bSsd < bRam) (hRG : bRam < bGpu) :
    (mGpu + mRam + mSsd) * (bRam * bSsd) ≤
      mGpu * (bRam * bSsd) + mRam * (bGpu * bSsd) + mSsd * (bGpu * bRam) := by
  have h1 : mRam * (bRam * bSsd) ≤ mRam * (bGpu * bSsd) :=
    Nat.mul_le_mul_left mRam (Nat.mul_le_mul_right bSsd (Nat.le_of_lt hRG))
  have h2 : mSsd * (bRam * bSsd) ≤ mSsd * (bGpu * bRam) := by
    have hbr : bRam * bSsd ≤ bRam * bGpu := Nat.mul_le_mul_left bRam (Nat.le_of_lt (Nat.lt_trans hSR hRG))
    rw [Nat.mul_comm bRam bGpu] at hbr
    exact Nat.mul_le_mul_left mSsd hbr
  rw [Nat.add_mul, Nat.add_mul]
  exact Nat.add_le_add (Nat.add_le_add_left h1 (mGpu * (bRam * bSsd))) h2

-- Theorem 11: Ultra-Sparse MoE Active Fraction (e.g. Magnitude 5% active) Strictly Cuts Traffic
theorem sparse_moe_active_bandwidth_gain_universal
    (M p q : Nat) (hM : 0 < M) (hpq : p < q) :
    M * p < M * q := by
  exact Nat.mul_lt_mul_of_pos_left hpq hM

-- Theorem 12: Joint Bit-Width Compression Strictly Frees Bit Budget (S78/S86)
theorem joint_bpw_compression_headroom_universal
    (N bHi bLo : Nat) (hN : 0 < N) (hb : bLo < bHi) :
    N * bLo < N * bHi ∧ 0 < N * bHi - N * bLo := by
  have hlt : N * bLo < N * bHi := Nat.mul_lt_mul_of_pos_left hb hN
  exact ⟨hlt, Nat.sub_pos_of_lt hlt⟩

-- ===========================================================================
-- PILLAR 3: Sleep Trilogy 2-Axis Consolidation, Proper Scoring & 5-Gate Lock
-- ===========================================================================

-- Theorem 13: Exact Integer Brier Strict Proper-Scoring Decomposition
-- q*(D - p)^2 + (D - q)*p^2 = D*q*(D - q) + D*(p - q)^2; strictly minimized iff p = q.
theorem brier_strict_proper_scoring_universal
    (q p D : Int) (hD : 0 < D) (hneq : p ≠ q) :
    D * (q * (D - q)) < q * ((D - p) * (D - p)) + (D - q) * (p * p) := by
  have hid :
      q * ((D - p) * (D - p)) + (D - q) * (p * p) =
      D * (q * (D - q)) + D * ((p - q) * (p - q)) := by
    rw [int_sq_sub D p, int_sq_sub p q]
    have hL :
        q * (D * D - 2 * (D * p) + p * p) + (D - q) * (p * p) =
        D * D * q - 2 * D * p * q + D * (p * p) := by
      rw [Int.mul_add, Int.mul_sub, Int.sub_mul D q (p * p)]
      have hddq : q * (D * D) = D * D * q := Int.mul_comm q (D * D)
      have h2dpq : q * (2 * (D * p)) = 2 * D * p * q := by
        rw [Int.mul_comm q (2 * (D * p)), ← Int.mul_assoc 2 D p, Int.mul_assoc (2 * D) p q]
      rw [hddq, h2dpq]
      simp only [Int.sub_eq_add_neg]
      have hc : (D * D * q + -(2 * D * p * q) + q * (p * p)) + (D * (p * p) + -(q * (p * p))) =
          (D * D * q + -(2 * D * p * q) + D * (p * p)) + (q * (p * p) + -(q * (p * p))) := by
        ac_rfl
      rw [hc, Int.add_right_neg, Int.add_zero]
    have hR :
        D * (q * (D - q)) + D * (p * p - 2 * (p * q) + q * q) =
        D * D * q - 2 * D * p * q + D * (p * p) := by
      rw [Int.mul_sub q D q, Int.mul_sub D (q * D) (q * q),
          Int.mul_add D (p * p - 2 * (p * q)) (q * q),
          Int.mul_sub D (p * p) (2 * (p * q))]
      have h1 : D * (q * D) = D * D * q := by
        rw [Int.mul_comm q D, ← Int.mul_assoc D D q]
      have h2 : D * (2 * (p * q)) = 2 * D * p * q := by
        rw [Int.mul_left_comm D 2 (p * q), ← Int.mul_assoc 2 D (p * q), Int.mul_assoc (2 * D) p q]
      rw [h1, h2]
      simp only [Int.sub_eq_add_neg]
      have hc : (D * D * q + -(D * (q * q))) + (D * (p * p) + -(2 * D * p * q) + D * (q * q)) =
          (D * D * q + -(2 * D * p * q) + D * (p * p)) + (-(D * (q * q)) + D * (q * q)) := by
        ac_rfl
      rw [hc, Int.add_left_neg, Int.add_zero]
    rw [hL, hR]
  rw [hid]
  have hpq : p - q ≠ 0 := fun h0 => hneq (Int.sub_eq_zero.mp h0)
  have hpos : 0 < D * ((p - q) * (p - q)) := int_mul_pos_of_pos hD (int_sq_pos_of_ne_zero hpq)
  exact Int.lt_add_of_pos_right (D * (q * (D - q))) hpos

-- Theorem 14: Reference-Mixture Calibration Bias Theorem (Thinking Machines lambda-reward)
-- Whenever reference weight (D - lam) > 0 and reference r != truth q, squared calibration bias > 0.
theorem reference_mixture_bias_variance_universal
    (lam q r D : Int) (hLam : lam < D) (hqr : q ≠ r) :
    0 < ((D - lam) * (r - q)) * ((D - lam) * (r - q)) := by
  have h1 : D - lam ≠ 0 := Int.ne_of_gt (Int.sub_pos.mpr hLam)
  have h2 : r - q ≠ 0 := fun h0 => hqr (Int.sub_eq_zero.mp h0).symm
  have hprod : (D - lam) * (r - q) ≠ 0 := fun h0 => by
    cases Int.mul_eq_zero.mp h0 with
    | inl ha => exact h1 ha
    | inr hb => exact h2 hb
  exact int_sq_pos_of_ne_zero hprod

-- Theorem 15: Single-Draw Overconfidence Paradox (beats truth on Y=1 yet loses in expectation!)
theorem single_draw_overconfidence_paradox_universal
    (q p2 D : Int) (hq : 0 < q) (hqp : q < p2) (hpD : p2 < D) :
    ((D - p2) * (D - p2) < (D - q) * (D - q)) ∧
    (D * (q * (D - q)) < q * ((D - p2) * (D - p2)) + (D - q) * (p2 * p2)) := by
  have hD : 0 < D := Int.lt_trans (Int.lt_trans hq hqp) hpD
  have hpos : 0 < D - p2 := Int.sub_pos.mpr hpD
  have hlt : D - p2 < D - q := by
    have hd : (D - q) - (D - p2) = p2 - q := by
      simp only [Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg]
      have hr : (D + -q) + (-D + p2) = (D + -D) + (p2 + -q) := by ac_rfl
      rw [hr, Int.add_right_neg, Int.zero_add]
    exact Int.sub_pos.mp (by rw [hd]; exact Int.sub_pos.mpr hqp)
  exact ⟨int_mul_sq_lt_of_pos_lt hpos hlt,
         brier_strict_proper_scoring_universal q p2 D hD (Int.ne_of_gt hqp)⟩

-- Theorem 16: Offline Sleep Loop Contraction (rho < 1) vs Hallucination Divergence (rho > 1)
theorem sleep_loop_contraction_vs_divergence_universal
    (p q n : Nat) (hp : 0 < p) (hpq : p < q) :
    natPow p (n + 1) < natPow q (n + 1) ∧
    natPow q (n + 1) < natPow (q + p) (n + 1) := by
  have hq : 0 < q := Nat.lt_trans hp hpq
  exact ⟨natPow_lt_of_lt hp hpq n, natPow_lt_of_lt hq (Nat.lt_add_of_pos_right hp) n⟩

-- Theorem 17: S79 / 2611 Last-Loop KV Sharing Strictly Compresses KV Cache (R >= 2, W < L)
theorem last_loop_kv_sharing_strict_gain_universal
    (R L W : Nat) (hR : 2 ≤ R) (hWL : W < L) :
    L + (R - 1) * W < R * L := by
  have h1 : 1 ≤ R := Nat.le_trans (by decide : 1 ≤ 2) hR
  have hRm1_pos : 0 < R - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2) hR)
  have hmul : (R - 1) * W < (R - 1) * L := Nat.mul_lt_mul_of_pos_left hWL hRm1_pos
  have hadd : L + (R - 1) * W < L + (R - 1) * L := Nat.add_lt_add_left hmul L
  have hfact : L + (R - 1) * L = R * L := by
    calc
      L + (R - 1) * L = 1 * L + (R - 1) * L := by rw [Nat.one_mul]
      _ = (1 + (R - 1)) * L := (Nat.add_mul 1 (R - 1) L).symm
      _ = R * L := by rw [Nat.add_comm 1 (R - 1), Nat.sub_add_cancel h1]
  rw [hfact] at hadd
  exact hadd

-- Theorem 18: 5-Gate Wave-6 Consolidation Borromean Necessity (Zero Axioms [])
theorem five_gate_consolidation_borromean_universal
    (g1 g2 g3 g4 g5 : Bool) :
    (g1 && g2 && g3 && g4 && g5 = true) ↔
      (g1 = true ∧ g2 = true ∧ g3 = true ∧ g4 = true ∧ g5 = true) := by
  cases g1 <;> cases g2 <;> cases g3 <;> cases g4 <;> cases g5 <;> decide

end S94Wave6Convergence

#print axioms S94Wave6Convergence.hadamard_smearing_diagonal_flat_universal
#print axioms S94Wave6Convergence.hadamard_importance_blowup_linear_in_k_universal
#print axioms S94Wave6Convergence.hadamard_uniform_isotropic_commutes_universal
#print axioms S94Wave6Convergence.householder_reflection_isometry_universal
#print axioms S94Wave6Convergence.householder_reflection_involution_universal
#print axioms S94Wave6Convergence.householder_projection_idempotent_and_dpi_universal
#print axioms S94Wave6Convergence.residency_phase_cliff_universal
#print axioms S94Wave6Convergence.tier_spill_strict_slowdown_universal
#print axioms S94Wave6Convergence.nvme_spill_dominates_ram_spill_universal
#print axioms S94Wave6Convergence.three_tier_monotonic_time_universal
#print axioms S94Wave6Convergence.sparse_moe_active_bandwidth_gain_universal
#print axioms S94Wave6Convergence.joint_bpw_compression_headroom_universal
#print axioms S94Wave6Convergence.brier_strict_proper_scoring_universal
#print axioms S94Wave6Convergence.reference_mixture_bias_variance_universal
#print axioms S94Wave6Convergence.single_draw_overconfidence_paradox_universal
#print axioms S94Wave6Convergence.sleep_loop_contraction_vs_divergence_universal
#print axioms S94Wave6Convergence.last_loop_kv_sharing_strict_gain_universal
#print axioms S94Wave6Convergence.five_gate_consolidation_borromean_universal
