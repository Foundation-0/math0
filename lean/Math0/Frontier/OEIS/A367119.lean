/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A367119
import Math0.Audit

/-!
# Edges of the all-chords graph of a triangle with `n` general points per side (A367119)

We prove the conjecture of Shannon and Sloane in the form of `statement`: for every `n` and every
placement `B` of `n` points on each side of the equilateral triangle in general position, the
planar graph has `(3/2)(3n^4 + 4n^3 + 3n^2 + 4n + 2)` edges.

*Parameters.* The boundary is parametrized by `P : [0, 3) → ℂ` (side `j` is the parameter range
`[j, j + 1]`, the corner `0` being the parameter `0`), with left inverse `θ`. The boundary points
are `B = P '' T` for a set `T ⊆ [0, 3)` of `3n + 3` parameters, `n + 2` on each closed side
(`exists_T`). For parameters `a < b < c` not all on one side, the signed area
`D (P a) (P b) (P c)` is positive (`E_pos`, a short computation on each pattern of sides). Hence
a chord `[P a, P b]` (`a < b` not on a common side) has the boundary points with parameters in
`(a, b)` strictly on one side and the others strictly on the other side; its relative interior
lies in the interior of the triangle; two chords meet in the interior iff their parameters
interleave (`X_mem`, `crossR_of_mem`), and then in exactly one point.

*Vertices and edges.* Using general position, the vertices on a chord `c` are its two endpoints
and one crossing point for each chord crossing `c`, all distinct (`V_chord`, `VC_card`); the
vertices on a side are the points of `B` on it (`V_side`, which also uses that two pieces of a
side meeting in a single point meet at a point of `B`, `oneD`). The edges are the consecutive
pairs of vertices on the three sides and on the chords, and these families are disjoint
(`edgeSet_eq`, `EF_card`). So the number of edges is
`3(n + 1) + #chords + ∑_c #(chords crossing c)` (`edges_eq`).

*Counting.* There are `3n(n + 1)` chords (`chords_card`). Crossing pairs of chords correspond to
the 4-subsets of `T` with no three points on a side (the two diagonals of the sorted quadruple,
`crossH_card`, `diag_iff`), and inclusion-exclusion gives
`C(3n+3, 4) - 3((2n+1) C(n+2, 3) + C(n+2, 4)) = (3/4) n^2 (n+1)(3n+1)` of them
(`crossings_formula`). Adding up gives the formula.
-/

namespace Math0.Frontier.A367119
open Math0.Statements.A367119

/-- Twice the signed area of the triangle `a b c`. -/
private noncomputable def D (a b c : ℂ) : ℝ := (b - a).re * (c - a).im - (b - a).im * (c - a).re

/-- The signed area vanishes when the third point is the first. -/
private lemma D_left (a b : ℂ) : D a b a = 0 := by simp [D]

/-- The signed area vanishes when the third point is the second. -/
private lemma D_right (a b : ℂ) : D a b b = 0 := by simp only [D]; ring

/-- `D a b` is affine in its third argument. -/
private lemma D_comb (a b p q : ℂ) (s t : ℝ) (h : s + t = 1) :
    D a b (s • p + t • q) = s * D a b p + t * D a b q := by
  have hs : s = 1 - t := by linarith
  subst hs
  simp only [D, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- A point of the segment `[a, b]` lies on the line `ab`. -/
private lemma D_of_mem_segment {a b z : ℂ} (h : z ∈ segment ℝ a b) : D a b z = 0 := by
  obtain ⟨s, t, -, -, hst, rfl⟩ := h
  rw [D_comb _ _ _ _ _ _ hst, D_left, D_right]; ring

/-- If `c` is not on the line `ab`, the segments `[a, b]` and `[c, d]` meet in at most one point. -/
private lemma seg_inter_sub {a b c d z z' : ℂ} (hc : D a b c ≠ 0) (hz1 : z ∈ segment ℝ a b)
    (hz2 : z ∈ segment ℝ c d) (hz1' : z' ∈ segment ℝ a b) (hz2' : z' ∈ segment ℝ c d) :
    z = z' := by
  have e1 := D_of_mem_segment hz1
  have e2 := D_of_mem_segment hz1'
  obtain ⟨s, t, -, -, hst, rfl⟩ := hz2
  obtain ⟨s', t', -, -, hst', rfl⟩ := hz2'
  rw [D_comb _ _ _ _ _ _ hst] at e1
  rw [D_comb _ _ _ _ _ _ hst'] at e2
  have htt : t = t' := by
    by_contra hne
    have hm : (t - t') * (D a b d - D a b c) = 0 := by
      have hs : s = 1 - t := by linarith
      have hs' : s' = 1 - t' := by linarith
      subst hs hs'
      linear_combination e1 - e2
    rcases mul_eq_zero.1 hm with h | h
    · exact hne (by linarith)
    · apply hc
      have hs : s = 1 - t := by linarith
      subst hs
      have : D a b d = D a b c := by linarith
      rw [this] at e1
      linarith
  have hss : s = s' := by linarith
  rw [htt, hss]

/-- `D a b` is positive on an open segment whose endpoints have nonnegative values, not both
zero. -/
private lemma openSeg_pos {a b c d z : ℂ} (hc : 0 ≤ D a b c) (hd : 0 ≤ D a b d)
    (h : 0 < D a b c ∨ 0 < D a b d) (hz : z ∈ openSegment ℝ c d) : 0 < D a b z := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  rw [D_comb _ _ _ _ _ _ hst]
  rcases h with h | h
  · have := mul_pos hs h
    have := mul_nonneg ht.le hd
    linarith
  · have := mul_pos ht h
    have := mul_nonneg hs.le hc
    linarith

/-- `D a b` is positive on a segment whose endpoints have positive values. -/
private lemma seg_pos {a b c d z : ℂ} (hc : 0 < D a b c) (hd : 0 < D a b d)
    (hz : z ∈ segment ℝ c d) : 0 < D a b z := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  rw [D_comb _ _ _ _ _ _ hst]
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    have : t = 1 := by linarith
    subst this; linarith
  · have := mul_pos h hc
    have := mul_nonneg ht hd.le
    linarith

/-- `D a b` is negative on a segment whose endpoints have negative values. -/
private lemma seg_neg {a b c d z : ℂ} (hc : D a b c < 0) (hd : D a b d < 0)
    (hz : z ∈ segment ℝ c d) : D a b z < 0 := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  rw [D_comb _ _ _ _ _ _ hst]
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    have : t = 1 := by linarith
    subst this; linarith
  · have := mul_neg_of_pos_of_neg h hc
    have := mul_nonpos_of_nonneg_of_nonpos ht hd.le
    linarith

/-- The intersection point of the lines `ab` and `cd`. -/
private noncomputable def crossPt (a b c d : ℂ) : ℂ :=
  (1 / (D a b c - D a b d)) • ((D a b c) • d - (D a b d) • c)

/-- Coefficients of the intersection point of two crossing segments. -/
private lemma opp_coeffs {x y : ℝ} (h : x * y < 0) : 0 < x / (x - y) ∧ 0 < -y / (x - y) := by
  rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at h) with hx | hx
  · have hy : 0 < y := by nlinarith
    have : x - y < 0 := by linarith
    exact ⟨div_pos_of_neg_of_neg hx this, div_pos_of_neg_of_neg (by linarith) this⟩
  · have hy : y < 0 := by nlinarith
    have : 0 < x - y := by linarith
    exact ⟨div_pos hx this, div_pos (by linarith) this⟩

/-- If `c, d` are strictly on opposite sides of the line `ab` and vice versa, the two open
segments meet at `crossPt a b c d`. -/
private lemma crossPt_mem {a b c d : ℂ} (h1 : D a b c * D a b d < 0) (h2 : D c d a * D c d b < 0) :
    crossPt a b c d ∈ openSegment ℝ a b ∧ crossPt a b c d ∈ openSegment ℝ c d := by
  have hne : D a b c - D a b d ≠ 0 := by
    intro h; have : D a b c = D a b d := by linarith
    rw [this] at h1; nlinarith
  have hid : D c d b - D c d a = D a b c - D a b d := by
    simp only [D, Complex.sub_re, Complex.sub_im]; ring
  have hne' : D c d b - D c d a ≠ 0 := by rw [hid]; exact hne
  constructor
  · obtain ⟨p1, p2⟩ := opp_coeffs (show D c d b * D c d a < 0 by linarith)
    refine ⟨D c d b / (D c d b - D c d a), -D c d a / (D c d b - D c d a), p1, p2, ?_, ?_⟩
    · field_simp; ring
    · rw [hid]
      simp only [D, Complex.sub_re, Complex.sub_im] at hne
      apply Complex.ext <;>
      · simp only [crossPt, D, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
          Complex.sub_re, Complex.sub_im, smul_eq_mul]
        field_simp
        ring
  · obtain ⟨p1, p2⟩ := opp_coeffs h1
    refine ⟨-D a b d / (D a b c - D a b d), D a b c / (D a b c - D a b d), p2, p1, ?_, ?_⟩
    · field_simp; ring
    · apply Complex.ext <;>
      · simp only [crossPt, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
          Complex.sub_re, Complex.sub_im, smul_eq_mul]
        field_simp
        ring

/-! ### The boundary parametrization -/

/-- The real part of the boundary point with parameter `t`. -/
private noncomputable def xP (t : ℝ) : ℝ := if t ≤ 1 then t else (3 - t) / 2
/-- The imaginary part, divided by `√3`, of the boundary point with parameter `t`. -/
private noncomputable def yP (t : ℝ) : ℝ :=
  if t ≤ 1 then 0 else if t ≤ 2 then (t - 1) / 2 else (3 - t) / 2

/-- The boundary point with parameter `t ∈ [0, 3)`. -/
private noncomputable def P (t : ℝ) : ℂ := ⟨xP t, Real.sqrt 3 * yP t⟩

/-- `D (P a) (P b) (P c) / √3`. -/
private noncomputable def E (a b c : ℝ) : ℝ :=
  (xP b - xP a) * (yP c - yP a) - (yP b - yP a) * (xP c - xP a)

/-- The signed area of three boundary points. -/
private lemma D_P (a b c : ℝ) : D (P a) (P b) (P c) = Real.sqrt 3 * E a b c := by
  simp only [D, P, E, Complex.sub_re, Complex.sub_im]; ring

/-- `E` is invariant under cyclic permutation. -/
private lemma E_cyc (a b c : ℝ) : E a b c = E b c a := by simp only [E]; ring
/-- `E` changes sign when the last two arguments are swapped. -/
private lemma E_swap (a b c : ℝ) : E a b c = - E a c b := by simp only [E]; ring

/-- `xP` on the parameter range of side 0. -/
private lemma xP_A {t : ℝ} (h : t ≤ 1) : xP t = t := by simp [xP, h]
/-- `yP` on the parameter range of side 0. -/
private lemma yP_A {t : ℝ} (h : t ≤ 1) : yP t = 0 := by simp [yP, h]
/-- `xP` on the parameter range of sides 1 and 2. -/
private lemma xP_B {t : ℝ} (h : 1 < t) : xP t = (3 - t) / 2 := by simp [xP, not_le.2 h]
/-- `yP` on the parameter range of side 1. -/
private lemma yP_B {t : ℝ} (h : 1 < t) (h' : t ≤ 2) : yP t = (t - 1) / 2 := by
  simp [yP, not_le.2 h, h']
/-- `yP` on the parameter range of side 2. -/
private lemma yP_C {t : ℝ} (h : 2 < t) : yP t = (3 - t) / 2 := by
  simp [yP, not_le.2 h, not_le.2 (by linarith : (1:ℝ) < t)]

/-- The parameter `t ∈ [0, 3)` belongs to the closed side 0. -/
private def S0 (t : ℝ) : Prop := t ≤ 1
/-- The parameter `t ∈ [0, 3)` belongs to the closed side 1. -/
private def S1 (t : ℝ) : Prop := 1 ≤ t ∧ t ≤ 2
/-- The parameter `t ∈ [0, 3)` belongs to the closed side 2 (which contains the corner `0`). -/
private def S2 (t : ℝ) : Prop := 2 ≤ t ∨ t = 0

/-- Decidability of `S0`. -/
private noncomputable instance : DecidablePred S0 := fun t => by unfold S0; infer_instance
/-- Decidability of `S1`. -/
private noncomputable instance : DecidablePred S1 := fun t => by unfold S1; infer_instance
/-- Decidability of `S2`. -/
private noncomputable instance : DecidablePred S2 := fun t => by unfold S2; infer_instance

/-- Two parameters lie on a common closed side. -/
private def coSide (a b : ℝ) : Prop := (S0 a ∧ S0 b) ∨ (S1 a ∧ S1 b) ∨ (S2 a ∧ S2 b)
/-- Three parameters lie on a common closed side. -/
private def coSide3 (a b c : ℝ) : Prop :=
  (S0 a ∧ S0 b ∧ S0 c) ∨ (S1 a ∧ S1 b ∧ S1 c) ∨ (S2 a ∧ S2 b ∧ S2 c)

/-- Orientation of three boundary points in increasing parameter order. -/
private lemma E_pos {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hc : c < 3)
    (h : ¬ coSide3 a b c) : 0 < E a b c := by
  unfold coSide3 S0 S1 S2 at h
  unfold E
  rcases le_or_gt c 1 with hc1 | hc1
  · exact absurd (Or.inl ⟨by linarith, by linarith, hc1⟩) h
  rcases le_or_gt c 2 with hc2 | hc2
  · rw [xP_B hc1, yP_B hc1 hc2]
    rcases le_or_gt b 1 with hb1 | hb1
    · rw [xP_A hb1, yP_A hb1, xP_A (by linarith : a ≤ 1), yP_A (by linarith : a ≤ 1)]
      nlinarith [mul_pos (sub_pos.2 hab) (sub_pos.2 hc1)]
    · rw [xP_B hb1, yP_B hb1 (by linarith)]
      rcases le_or_gt a 1 with ha1 | ha1
      · rw [xP_A ha1, yP_A ha1]
        have ha1' : a < 1 := by
          rcases lt_or_eq_of_le ha1 with h1 | h1
          · exact h1
          · exact absurd (Or.inr (Or.inl ⟨⟨h1.ge, by linarith⟩, ⟨by linarith, by linarith⟩,
              ⟨by linarith, hc2⟩⟩)) h
        nlinarith [mul_pos (sub_pos.2 hbc) (sub_pos.2 ha1')]
      · exact absurd (Or.inr (Or.inl ⟨⟨ha1.le, by linarith⟩, ⟨by linarith, by linarith⟩,
          ⟨by linarith, hc2⟩⟩)) h
  · rw [xP_B hc1, yP_C hc2]
    rcases le_or_gt b 1 with hb1 | hb1
    · rw [xP_A hb1, yP_A hb1, xP_A (by linarith : a ≤ 1), yP_A (by linarith : a ≤ 1)]
      nlinarith [mul_pos (sub_pos.2 hab) (sub_pos.2 hc)]
    rcases le_or_gt b 2 with hb2 | hb2
    · rw [xP_B hb1, yP_B hb1 hb2]
      rcases le_or_gt a 1 with ha1 | ha1
      · rw [xP_A ha1, yP_A ha1]
        rcases eq_or_lt_of_le ha with h0 | h0
        · have hb2' : b < 2 := by
            rcases lt_or_eq_of_le hb2 with h2 | h2
            · exact h2
            · exact absurd (Or.inr (Or.inr ⟨Or.inr h0.symm, Or.inl h2.ge, Or.inl hc2.le⟩)) h
          rw [← h0]
          nlinarith [mul_pos (sub_pos.2 hb2') (sub_pos.2 hc)]
        · nlinarith [mul_pos (mul_pos h0 (sub_pos.2 hb1)) (sub_pos.2 hc2),
            mul_nonneg (mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hc.le)) (sub_nonneg.2 ha1)]
      · rw [xP_B ha1, yP_B ha1 (by linarith)]
        nlinarith [mul_pos (sub_pos.2 hab) (sub_pos.2 hc2)]
    · rw [xP_B hb1, yP_C hb2]
      rcases le_or_gt a 1 with ha1 | ha1
      · rw [xP_A ha1, yP_A ha1]
        have h0 : 0 < a := by
          rcases eq_or_lt_of_le ha with h0 | h0
          · exact absurd (Or.inr (Or.inr ⟨Or.inr h0.symm, Or.inl hb2.le, Or.inl hc2.le⟩)) h
          · exact h0
        nlinarith [mul_pos h0 (sub_pos.2 hbc)]
      rcases le_or_gt a 2 with ha2 | ha2
      · rw [xP_B ha1, yP_B ha1 ha2]
        have ha2' : a < 2 := by
          rcases lt_or_eq_of_le ha2 with h2 | h2
          · exact h2
          · exact absurd (Or.inr (Or.inr ⟨Or.inl h2.ge, Or.inl hb2.le, Or.inl hc2.le⟩)) h
        nlinarith [mul_pos (sub_pos.2 hbc) (sub_pos.2 ha2')]
      · exact absurd (Or.inr (Or.inr ⟨Or.inl ha2.le, Or.inl hb2.le, Or.inl hc2.le⟩)) h

/-- The corner `0`. -/
private lemma corner_zero : corner 0 = 0 := by simp [corner]
/-- The corner `1`. -/
private lemma corner_one : corner 1 = 1 := by simp [corner]
/-- The corner `1/2 + (√3/2) i`. -/
private lemma corner_two : corner 2 = ⟨1 / 2, Real.sqrt 3 / 2⟩ := by simp [corner]

/-- The parameter `0` gives the corner `0`. -/
private lemma P_zero : P 0 = corner 0 := by
  rw [corner_zero]; apply Complex.ext <;> simp [P, xP, yP]
/-- The parameter `1` gives the corner `1`. -/
private lemma P_one : P 1 = corner 1 := by
  rw [corner_one]; apply Complex.ext <;> simp [P, xP, yP]
/-- The parameter `2` gives the corner `2`. -/
private lemma P_two : P 2 = corner 2 := by
  rw [corner_two]; apply Complex.ext <;> norm_num [P, xP, yP]
  ring

/-- `√3 > 0`. -/
private lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

/-- The parameter of a boundary point. -/
private noncomputable def θ (z : ℂ) : ℝ := if z.im = 0 then z.re else 3 - 2 * z.re

/-- `yP` is positive off side 0. -/
private lemma yP_pos {t : ℝ} (h1 : 1 < t) (h3 : t < 3) : 0 < yP t := by
  rcases le_or_gt t 2 with h2 | h2
  · rw [yP_B h1 h2]; linarith
  · rw [yP_C h2]; linarith

/-- `yP` is nonnegative. -/
private lemma yP_nonneg {t : ℝ} (h3 : t < 3) : 0 ≤ yP t := by
  rcases le_or_gt t 1 with h1 | h1
  · rw [yP_A h1]
  · exact (yP_pos h1 h3).le

/-- `θ` inverts `P` on `[0, 3)`. -/
private lemma θ_P {t : ℝ} (_h0 : 0 ≤ t) (h3 : t < 3) : θ (P t) = t := by
  unfold θ
  rcases le_or_gt t 1 with h1 | h1
  · have : (P t).im = 0 := by simp [P, yP_A h1]
    rw [if_pos this]; simp [P, xP_A h1]
  · have : (P t).im ≠ 0 := by
      simp only [P]
      exact (mul_pos sqrt3_pos (yP_pos h1 h3)).ne'
    rw [if_neg this]; simp only [P, xP_B h1]; ring

/-- `P` is injective on `[0, 3)`. -/
private lemma P_inj {s t : ℝ} (hs0 : 0 ≤ s) (hs3 : s < 3) (ht0 : 0 ≤ t) (ht3 : t < 3)
    (h : P s = P t) : s = t := by
  rw [← θ_P hs0 hs3, ← θ_P ht0 ht3, h]

/-! ### Corner lines -/

/-- The line through the corners `0` and `1` at a boundary point. -/
private lemma D01 (t : ℝ) : D (corner 0) (corner 1) (P t) = Real.sqrt 3 * yP t := by
  rw [← P_zero, ← P_one, D_P]
  congr 1
  simp only [E, xP_A (show (0:ℝ) ≤ 1 by norm_num), yP_A (show (0:ℝ) ≤ 1 by norm_num),
    xP_A (show (1:ℝ) ≤ 1 by norm_num), yP_A (show (1:ℝ) ≤ 1 by norm_num)]
  ring

/-- The line through the corners `1` and `2` at a boundary point. -/
private lemma D12 (t : ℝ) :
    D (corner 1) (corner 2) (P t) = Real.sqrt 3 * ((1 - xP t - yP t) / 2) := by
  rw [← P_one, ← P_two, D_P]
  congr 1
  simp only [E, xP_A (show (1:ℝ) ≤ 1 by norm_num), yP_A (show (1:ℝ) ≤ 1 by norm_num),
    xP_B (show (1:ℝ) < 2 by norm_num), yP_B (show (1:ℝ) < 2 by norm_num) (le_refl _)]
  ring

/-- The line through the corners `2` and `0` at a boundary point. -/
private lemma D20 (t : ℝ) : D (corner 2) (corner 0) (P t) = Real.sqrt 3 * ((xP t - yP t) / 2) := by
  rw [← P_zero, ← P_two, D_P]
  congr 1
  simp only [E, xP_A (show (0:ℝ) ≤ 1 by norm_num), yP_A (show (0:ℝ) ≤ 1 by norm_num),
    xP_B (show (1:ℝ) < 2 by norm_num), yP_B (show (1:ℝ) < 2 by norm_num) (le_refl _)]
  ring

/-- Boundary points are on the inner side of side 0. -/
private lemma L0_nonneg {t : ℝ} (_h0 : 0 ≤ t) (h3 : t < 3) : 0 ≤ yP t := yP_nonneg h3

/-- Boundary points off side 0 are strictly on its inner side. -/
private lemma L0_pos_iff {t : ℝ} (_h0 : 0 ≤ t) (h3 : t < 3) : 0 < yP t ↔ ¬ S0 t := by
  unfold S0
  constructor
  · intro h h1; rw [yP_A h1] at h; exact lt_irrefl _ h
  · intro h; exact yP_pos (not_le.1 h) h3

/-- Boundary points are on the inner side of side 1. -/
private lemma L1_nonneg {t : ℝ} (_h0 : 0 ≤ t) (_h3 : t < 3) : 0 ≤ (1 - xP t - yP t) / 2 := by
  rcases le_or_gt t 1 with h1 | h1
  · rw [xP_A h1, yP_A h1]; linarith
  rcases le_or_gt t 2 with h2 | h2
  · rw [xP_B h1, yP_B h1 h2]; linarith
  · rw [xP_B h1, yP_C h2]; linarith

/-- Boundary points off side 1 are strictly on its inner side. -/
private lemma L1_pos_iff {t : ℝ} (_h0 : 0 ≤ t) (h3 : t < 3) :
    0 < (1 - xP t - yP t) / 2 ↔ ¬ S1 t := by
  unfold S1
  rcases le_or_gt t 1 with h1 | h1
  · rw [xP_A h1, yP_A h1]
    constructor
    · rintro h ⟨h1', -⟩; linarith
    · intro h
      have : t < 1 := by
        rcases lt_or_eq_of_le h1 with h' | h'
        · exact h'
        · exact absurd ⟨h'.ge, by linarith⟩ h
      linarith
  rcases le_or_gt t 2 with h2 | h2
  · rw [xP_B h1, yP_B h1 h2]
    constructor
    · intro h; linarith
    · intro h; exact absurd ⟨h1.le, h2⟩ h
  · rw [xP_B h1, yP_C h2]
    constructor
    · rintro h ⟨-, h'⟩; linarith
    · intro _; linarith

/-- Boundary points are on the inner side of side 2. -/
private lemma L2_nonneg {t : ℝ} (h0 : 0 ≤ t) (_h3 : t < 3) : 0 ≤ (xP t - yP t) / 2 := by
  rcases le_or_gt t 1 with h1 | h1
  · rw [xP_A h1, yP_A h1]; linarith
  rcases le_or_gt t 2 with h2 | h2
  · rw [xP_B h1, yP_B h1 h2]; linarith
  · rw [xP_B h1, yP_C h2]; linarith

/-- Boundary points off side 2 are strictly on its inner side. -/
private lemma L2_pos_iff {t : ℝ} (h0 : 0 ≤ t) (_h3 : t < 3) : 0 < (xP t - yP t) / 2 ↔ ¬ S2 t := by
  unfold S2
  rcases le_or_gt t 1 with h1 | h1
  · rw [xP_A h1, yP_A h1]
    constructor
    · rintro h (h' | h') <;> linarith
    · intro h
      have : t ≠ 0 := fun h' => h (Or.inr h')
      have : 0 < t := lt_of_le_of_ne h0 (Ne.symm this)
      linarith
  rcases le_or_gt t 2 with h2 | h2
  · rw [xP_B h1, yP_B h1 h2]
    constructor
    · rintro h (h' | h') <;> linarith
    · intro h
      have : t < 2 := by
        rcases lt_or_eq_of_le h2 with h' | h'
        · exact h'
        · exact absurd (Or.inl h'.ge) h
      linarith
  · rw [xP_B h1, yP_C h2]
    constructor
    · intro h; linarith
    · intro h; exact absurd (Or.inl h2.le) h

/-- The three corner-line functionals at boundary points. -/
private lemma Dline_nonneg (j : Fin 3) {t : ℝ} (h0 : 0 ≤ t) (h3 : t < 3) :
    0 ≤ D (corner j) (corner (j + 1)) (P t) := by
  fin_cases j
  · show 0 ≤ D (corner 0) (corner 1) (P t)
    rw [D01]; exact mul_nonneg sqrt3_pos.le (L0_nonneg h0 h3)
  · show 0 ≤ D (corner 1) (corner 2) (P t)
    rw [D12]; exact mul_nonneg sqrt3_pos.le (L1_nonneg h0 h3)
  · show 0 ≤ D (corner 2) (corner 0) (P t)
    rw [D20]; exact mul_nonneg sqrt3_pos.le (L2_nonneg h0 h3)

/-- Side membership of a parameter. -/
private def Sd : Fin 3 → ℝ → Prop
  | ⟨0, _⟩, t => S0 t
  | ⟨1, _⟩, t => S1 t
  | ⟨2, _⟩, t => S2 t

/-- Decidability of `Sd j`. -/
private noncomputable instance (j : Fin 3) : DecidablePred (Sd j) := Classical.decPred _

/-- A boundary point is strictly inside the line of side `j` iff it is not on side `j`. -/
private lemma Dline_pos_iff (j : Fin 3) {t : ℝ} (h0 : 0 ≤ t) (h3 : t < 3) :
    0 < D (corner j) (corner (j + 1)) (P t) ↔ ¬ Sd j t := by
  fin_cases j
  · show 0 < D (corner 0) (corner 1) (P t) ↔ ¬ S0 t
    rw [D01, ← L0_pos_iff h0 h3]
    exact ⟨fun h => pos_of_mul_pos_right h sqrt3_pos.le, fun h => mul_pos sqrt3_pos h⟩
  · show 0 < D (corner 1) (corner 2) (P t) ↔ ¬ S1 t
    rw [D12, ← L1_pos_iff h0 h3]
    exact ⟨fun h => pos_of_mul_pos_right h sqrt3_pos.le, fun h => mul_pos sqrt3_pos h⟩
  · show 0 < D (corner 2) (corner 0) (P t) ↔ ¬ S2 t
    rw [D20, ← L2_pos_iff h0 h3]
    exact ⟨fun h => pos_of_mul_pos_right h sqrt3_pos.le, fun h => mul_pos sqrt3_pos h⟩

/-- `coSide` in terms of the indexed side predicate. -/
private lemma coSide_iff (a b : ℝ) : coSide a b ↔ ∃ j : Fin 3, Sd j a ∧ Sd j b := by
  unfold coSide
  constructor
  · rintro (h | h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨j, h⟩
    fin_cases j
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-! ### Sides -/

/-- The closed side `j`. -/
private def side (j : Fin 3) : Set ℂ := segment ℝ (corner j) (corner (j + 1))

/-- A parameter of side `j` gives a point of side `j`. -/
private lemma P_mem_side {j : Fin 3} {t : ℝ} (h0 : 0 ≤ t) (h3 : t < 3) (h : Sd j t) :
    P t ∈ side j := by
  fin_cases j
  · change S0 t at h; unfold S0 at h
    change P t ∈ segment ℝ (corner 0) (corner 1)
    rw [corner_zero, corner_one]
    refine ⟨1 - t, t, by linarith, h0, by ring, ?_⟩
    apply Complex.ext <;> simp [P, xP_A h, yP_A h]
  · change S1 t at h; unfold S1 at h
    change P t ∈ segment ℝ (corner 1) (corner 2)
    rw [corner_one, corner_two]
    rcases eq_or_lt_of_le h.1 with h1 | h1
    · subst h1
      refine ⟨1, 0, by norm_num, le_refl _, by ring, ?_⟩
      apply Complex.ext <;> simp [P, xP, yP]
    · refine ⟨2 - t, t - 1, by linarith, by linarith, by ring, ?_⟩
      apply Complex.ext <;> simp [P, xP_B h1, yP_B h1 h.2] <;> ring
  · change S2 t at h; unfold S2 at h
    change P t ∈ segment ℝ (corner 2) (corner 0)
    rw [corner_two, corner_zero]
    rcases h with h | h
    · rcases eq_or_lt_of_le h with h2 | h2
      · subst h2
        refine ⟨1, 0, by norm_num, le_refl _, by ring, ?_⟩
        apply Complex.ext <;> norm_num [P, xP, yP]
        ring
      · refine ⟨3 - t, t - 2, by linarith, by linarith, by ring, ?_⟩
        apply Complex.ext <;> simp [P, xP_B (by linarith : (1:ℝ) < t), yP_C h2] <;> ring
    · subst h
      refine ⟨0, 1, le_refl _, by norm_num, by ring, ?_⟩
      apply Complex.ext <;> simp [P, xP, yP]

/-- Every point of side `j` is `P t` for a parameter `t ∈ [0, 3)` of side `j`. -/
private lemma exists_P_of_mem_side {j : Fin 3} {z : ℂ} (hz : z ∈ side j) :
    ∃ t, 0 ≤ t ∧ t < 3 ∧ Sd j t ∧ P t = z := by
  fin_cases j
  · change z ∈ segment ℝ (corner 0) (corner 1) at hz
    change ∃ t, 0 ≤ t ∧ t < 3 ∧ S0 t ∧ P t = z
    rw [corner_zero, corner_one] at hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have hb1 : b ≤ 1 := by linarith
    refine ⟨b, hb, by linarith, hb1, ?_⟩
    apply Complex.ext <;> simp [P, xP_A hb1, yP_A hb1]
  · change z ∈ segment ℝ (corner 1) (corner 2) at hz
    change ∃ t, 0 ≤ t ∧ t < 3 ∧ S1 t ∧ P t = z
    rw [corner_one, corner_two] at hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    refine ⟨1 + b, by linarith, by linarith, ⟨by linarith, by linarith⟩, ?_⟩
    rcases eq_or_lt_of_le hb with h0 | h0
    · subst h0
      have : a = 1 := by linarith
      subst this
      apply Complex.ext <;> simp [P, xP, yP]
    · apply Complex.ext <;>
        simp [P, xP_B (by linarith : (1:ℝ) < 1 + b), yP_B (by linarith : (1:ℝ) < 1 + b)
          (by linarith : 1 + b ≤ 2)] <;> linarith
  · change z ∈ segment ℝ (corner 2) (corner 0) at hz
    change ∃ t, 0 ≤ t ∧ t < 3 ∧ S2 t ∧ P t = z
    rw [corner_two, corner_zero] at hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    rcases eq_or_lt_of_le ha with h0 | h0
    · subst h0
      have : b = 1 := by linarith
      subst this
      refine ⟨0, le_refl _, by norm_num, Or.inr rfl, ?_⟩
      apply Complex.ext <;> simp [P, xP, yP]
    · refine ⟨3 - a, by linarith, by linarith, Or.inl (by linarith), ?_⟩
      rcases eq_or_lt_of_le (show a ≤ 1 by linarith) with h1 | h1
      · subst h1
        apply Complex.ext <;> norm_num [P, xP, yP]
        ring
      · apply Complex.ext <;>
          simp [P, xP_B (by linarith : (1:ℝ) < 3 - a), yP_C (by linarith : (2:ℝ) < 3 - a)] <;>
          ring

/-- Points of side `j` lie on its line. -/
private lemma Dline_zero_of_mem_side (j : Fin 3) {z : ℂ} (hz : z ∈ side j) :
    D (corner j) (corner (j + 1)) z = 0 := D_of_mem_segment hz

/-- `P t` lies on side `j` iff `t` is a parameter of side `j`. -/
private lemma P_mem_side_iff {j : Fin 3} {t : ℝ} (h0 : 0 ≤ t) (h3 : t < 3) :
    P t ∈ side j ↔ Sd j t := by
  constructor
  · intro h
    by_contra hn
    have := (Dline_pos_iff j h0 h3).2 hn
    rw [Dline_zero_of_mem_side j h] at this
    exact lt_irrefl _ this
  · exact P_mem_side h0 h3

/-- Consecutive corners are distinct. -/
private lemma corner_ne (j : Fin 3) : corner j ≠ corner (j + 1) := by
  fin_cases j
  · show corner 0 ≠ corner 1
    rw [corner_zero, corner_one]; exact zero_ne_one
  · show corner 1 ≠ corner 2
    rw [corner_one, corner_two]; intro h
    have := congrArg Complex.im h
    simp at this; linarith [sqrt3_pos]
  · show corner 2 ≠ corner 0
    rw [corner_two, corner_zero]; intro h
    have := congrArg Complex.im h
    simp at this

/-- Points of the open side `j`. -/
private def Od : Fin 3 → ℝ → Prop
  | ⟨0, _⟩, t => 0 < t ∧ t < 1
  | ⟨1, _⟩, t => 1 < t ∧ t < 2
  | ⟨2, _⟩, t => 2 < t

/-- Decidability of `Od j`. -/
private noncomputable instance (j : Fin 3) : DecidablePred (Od j) := Classical.decPred _

/-- `P t` lies in the relative interior of side `j` iff `t` is in the open parameter interval of
side `j`. -/
private lemma P_mem_openSide_iff {j : Fin 3} {t : ℝ} (h0 : 0 ≤ t) (h3 : t < 3) :
    P t ∈ openSegment ℝ (corner j) (corner (j + 1)) ↔ Od j t := by
  have hne := corner_ne j
  constructor
  · intro h
    have hs : P t ∈ side j := openSegment_subset_segment _ _ _ h
    rw [P_mem_side_iff h0 h3] at hs
    have h1 : P t ≠ corner j := by
      intro e; rw [e, left_mem_openSegment_iff] at h; exact hne h
    have h2 : P t ≠ corner (j + 1) := by
      intro e; rw [e, right_mem_openSegment_iff] at h; exact hne h
    fin_cases j
    · change S0 t at hs; unfold S0 at hs
      change P t ≠ corner 0 at h1; change P t ≠ corner 1 at h2
      rw [← P_zero] at h1; rw [← P_one] at h2
      refine ⟨lt_of_le_of_ne h0 (fun e => h1 (by rw [← e])), lt_of_le_of_ne hs
        (fun e => h2 (by rw [e]))⟩
    · change S1 t at hs; unfold S1 at hs
      change P t ≠ corner 1 at h1; change P t ≠ corner 2 at h2
      rw [← P_one] at h1; rw [← P_two] at h2
      exact ⟨lt_of_le_of_ne hs.1 (fun e => h1 (by rw [← e])), lt_of_le_of_ne hs.2
        (fun e => h2 (by rw [e]))⟩
    · change S2 t at hs; unfold S2 at hs
      change P t ≠ corner 2 at h1; change P t ≠ corner 0 at h2
      rw [← P_two] at h1; rw [← P_zero] at h2
      rcases hs with hs | hs
      · exact lt_of_le_of_ne hs (fun e => h1 (by rw [← e]))
      · exact absurd (by rw [hs]) h2
  · intro h
    have hs : P t ∈ side j := by
      apply P_mem_side h0 h3
      fin_cases j
      · change 0 < t ∧ t < 1 at h; exact h.2.le
      · change 1 < t ∧ t < 2 at h; exact ⟨h.1.le, h.2.le⟩
      · change 2 < t at h; exact Or.inl h.le
    have hne1 : P t ≠ corner j := by
      fin_cases j
      · change 0 < t ∧ t < 1 at h; change P t ≠ corner 0
        rw [← P_zero]; intro e
        exact absurd (P_inj h0 h3 (le_refl _) (by norm_num) e) (ne_of_gt h.1)
      · change 1 < t ∧ t < 2 at h; change P t ≠ corner 1
        rw [← P_one]; intro e
        exact absurd (P_inj h0 h3 (by norm_num) (by norm_num) e) (ne_of_gt h.1)
      · change 2 < t at h; change P t ≠ corner 2
        rw [← P_two]; intro e
        exact absurd (P_inj h0 h3 (by norm_num) (by norm_num) e) (ne_of_gt h)
    have hne2 : P t ≠ corner (j + 1) := by
      fin_cases j
      · change 0 < t ∧ t < 1 at h; change P t ≠ corner 1
        rw [← P_one]; intro e
        exact absurd (P_inj h0 h3 (by norm_num) (by norm_num) e) (ne_of_lt h.2)
      · change 1 < t ∧ t < 2 at h; change P t ≠ corner 2
        rw [← P_two]; intro e
        exact absurd (P_inj h0 h3 (by norm_num) (by norm_num) e) (ne_of_lt h.2)
      · change 2 < t at h; change P t ≠ corner 0
        rw [← P_zero]; intro e
        have := P_inj h0 h3 (le_refl _) (by norm_num) e
        linarith
    rw [side, ← insert_endpoints_openSegment] at hs
    rcases hs with hs | hs | hs
    · exact absurd hs hne1
    · exact absurd hs hne2
    · exact hs

/-- Decidability of `coSide`. -/
private noncomputable instance : DecidableRel coSide := fun a b => by unfold coSide; infer_instance

/-- Two chords `(a, b)`, `(c, d)` (`a < b`, `c < d`) have interleaving endpoints. -/
private def crossR (c d : ℝ × ℝ) : Prop :=
  (c.1 < d.1 ∧ d.1 < c.2 ∧ c.2 < d.2) ∨ (d.1 < c.1 ∧ c.1 < d.2 ∧ d.2 < c.2)

/-- Decidability of `crossR c`. -/
private noncomputable instance (c : ℝ × ℝ) : DecidablePred (crossR c) := fun d => by
  unfold crossR; infer_instance

/-- The chords: pairs of parameters `a < b` of `T` not on a common side. -/
private noncomputable def Ch (T : Finset ℝ) : Finset (ℝ × ℝ) :=
  (T ×ˢ T).filter (fun p => p.1 < p.2 ∧ ¬ coSide p.1 p.2)

/-- Membership in `Ch T`. -/
private lemma mem_Ch {T : Finset ℝ} {c : ℝ × ℝ} :
    c ∈ Ch T ↔ c.1 ∈ T ∧ c.2 ∈ T ∧ c.1 < c.2 ∧ ¬ coSide c.1 c.2 := by
  simp only [Ch, Finset.mem_filter, Finset.mem_product, and_assoc]

/-! ### The region index -/

/-- The region index of a parameter: `0`, `(0,1)`, `1`, `(1,2)`, `2`, `(2,3)` give `0, …, 5`. -/
private noncomputable def ρ (t : ℝ) : ℕ :=
  if t ≤ 0 then 0 else if t < 1 then 1 else if t ≤ 1 then 2 else if t < 2 then 3
  else if t ≤ 2 then 4 else 5

/-- `S0` through the region index. -/
private lemma ρ_S0 {t : ℝ} (_h : 0 ≤ t) : S0 t ↔ ρ t ≤ 2 := by
  unfold S0 ρ
  split_ifs <;> constructor <;> intro hh <;>
    first | decide | (exfalso; linarith) | linarith

/-- `S1` through the region index. -/
private lemma ρ_S1 {t : ℝ} (_h : 0 ≤ t) : S1 t ↔ 2 ≤ ρ t ∧ ρ t ≤ 4 := by
  unfold S1 ρ
  split_ifs <;> constructor <;> intro hh <;>
    first | decide | (exfalso; linarith [hh.1, hh.2]) | (constructor <;> linarith)

/-- `S2` through the region index. -/
private lemma ρ_S2 {t : ℝ} (h : 0 ≤ t) : S2 t ↔ 4 ≤ ρ t ∨ ρ t = 0 := by
  unfold S2 ρ
  split_ifs <;> constructor <;> intro hh <;>
    first | decide | (exfalso; rcases hh with hh | hh <;> linarith) | (left; linarith) |
      (right; linarith) | omega | simp_all

/-- The region index is monotone, and constant only on open regions. -/
private lemma ρ_mono {s t : ℝ} (hs : 0 ≤ s) (h : s < t) :
    ρ s ≤ ρ t ∧ (ρ s = ρ t → ρ s = 1 ∨ ρ s = 3 ∨ ρ s = 5) := by
  unfold ρ
  split_ifs <;> first | decide | (exfalso; linarith)

/-- Three of four elements satisfy `p`. -/
private def three (p : ℝ → Prop) (w x y z : ℝ) : Prop :=
  (p w ∧ p x ∧ p y) ∨ (p w ∧ p x ∧ p z) ∨ (p w ∧ p y ∧ p z) ∨ (p x ∧ p y ∧ p z)

/-- At least three of four sorted points satisfy `p` iff `three p` holds. -/
private lemma three_le_card_filter (p : ℝ → Prop) [DecidablePred p] {w x y z : ℝ}
    (h1 : w < x) (h2 : x < y) (h3 : y < z) :
    3 ≤ (({w, x, y, z} : Finset ℝ).filter p).card ↔ three p w x y z := by
  have hwx : w ≠ x := ne_of_lt h1
  have hwy : w ≠ y := ne_of_lt (h1.trans h2)
  have hwz : w ≠ z := ne_of_lt (h1.trans (h2.trans h3))
  have hxy : x ≠ y := ne_of_lt h2
  have hxz : x ≠ z := ne_of_lt (h2.trans h3)
  have hyz : y ≠ z := ne_of_lt h3
  by_cases pw : p w <;> by_cases px : p x <;> by_cases py : p y <;> by_cases pz : p z <;>
    simp [three, Finset.filter_insert, Finset.filter_singleton, pw, px, py, pz, hwx, hwy, hwz,
      hxy, hxz, hyz]

/-- Reduction of `three` to a statement about region indices. -/
private lemma three_iff {w x y z : ℝ} (h0 : 0 ≤ w) (h1 : w < x) (h2 : x < y) (h3 : y < z)
    (p : ℝ → Prop) (q : ℕ → Prop) (hpq : ∀ t, 0 ≤ t → (p t ↔ q (ρ t)))
    (hq : ∀ a b c d : ℕ, a ≤ b → b ≤ c → c ≤ d → (a = b → a = 1 ∨ a = 3 ∨ a = 5) →
      (b = c → b = 1 ∨ b = 3 ∨ b = 5) → (c = d → c = 1 ∨ c = 3 ∨ c = 5) →
      (((q a ∧ q b ∧ q c) ∨ (q a ∧ q b ∧ q d) ∨ (q a ∧ q c ∧ q d) ∨ (q b ∧ q c ∧ q d)) ↔
        ((q a ∧ q c) ∨ (q b ∧ q d)))) :
    three p w x y z ↔ (p w ∧ p y) ∨ (p x ∧ p z) := by
  have hx : 0 ≤ x := by linarith
  have hy : 0 ≤ y := by linarith
  have hz : 0 ≤ z := by linarith
  have m1 := ρ_mono h0 h1
  have m2 := ρ_mono hx h2
  have m3 := ρ_mono hy h3
  unfold three
  rw [hpq w h0, hpq x hx, hpq y hy, hpq z hz]
  exact hq _ _ _ _ m1.1 m2.1 m3.1 m1.2 m2.2 m3.2

/-- For a sorted quadruple, three points lie on side 0 iff one of the diagonals does. -/
private lemma three_S0 {w x y z : ℝ} (h0 : 0 ≤ w) (h1 : w < x) (h2 : x < y) (h3 : y < z) :
    three S0 w x y z ↔ (S0 w ∧ S0 y) ∨ (S0 x ∧ S0 z) :=
  three_iff h0 h1 h2 h3 S0 (fun r => r ≤ 2) (fun t ht => ρ_S0 ht) (by intros; omega)

/-- For a sorted quadruple, three points lie on side 1 iff one of the diagonals does. -/
private lemma three_S1 {w x y z : ℝ} (h0 : 0 ≤ w) (h1 : w < x) (h2 : x < y) (h3 : y < z) :
    three S1 w x y z ↔ (S1 w ∧ S1 y) ∨ (S1 x ∧ S1 z) :=
  three_iff h0 h1 h2 h3 S1 (fun r => 2 ≤ r ∧ r ≤ 4) (fun t ht => ρ_S1 ht) (by intros; omega)

/-- For a sorted quadruple, three points lie on side 2 iff one of the diagonals does. -/
private lemma three_S2 {w x y z : ℝ} (h0 : 0 ≤ w) (h1 : w < x) (h2 : x < y) (h3 : y < z) :
    three S2 w x y z ↔ (S2 w ∧ S2 y) ∨ (S2 x ∧ S2 z) :=
  three_iff h0 h1 h2 h3 S2 (fun r => 4 ≤ r ∨ r = 0) (fun t ht => ρ_S2 ht) (by intros; omega)

/-- For a sorted quadruple, both diagonals are chords iff no three points share a side. -/
private lemma diag_iff {w x y z : ℝ} (h0 : 0 ≤ w) (h1 : w < x) (h2 : x < y) (h3 : y < z) :
    (¬ coSide w y ∧ ¬ coSide x z) ↔
      ¬ three S0 w x y z ∧ ¬ three S1 w x y z ∧ ¬ three S2 w x y z := by
  rw [three_S0 h0 h1 h2 h3, three_S1 h0 h1 h2 h3, three_S2 h0 h1 h2 h3]
  unfold coSide
  tauto

/-- Generalized Vandermonde count. -/
private lemma card_filter_card_eq {α : Type*} [DecidableEq α] (U : Finset α) (p : α → Prop)
    [DecidablePred p] (k m : ℕ) (hm : m ≤ k) :
    ((U.powersetCard k).filter (fun Q => (Q.filter p).card = m)).card =
      (U.filter p).card.choose m * (U.filter (fun x => ¬ p x)).card.choose (k - m) := by
  rw [← Finset.card_powersetCard m (U.filter p),
    ← Finset.card_powersetCard (k - m) (U.filter (fun x => ¬ p x)), ← Finset.card_product]
  symm
  apply Finset.card_nbij' (fun AR => AR.1 ∪ AR.2)
    (fun Q => (Q.filter p, Q.filter (fun x => ¬ p x)))
  · rintro ⟨A, R⟩ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powersetCard,
      Finset.subset_iff, Finset.mem_filter] at h
    obtain ⟨⟨hA, hAc⟩, ⟨hR, hRc⟩⟩ := h
    have hdis : Disjoint A R := by
      rw [Finset.disjoint_left]; intro x hx hx'; exact (hR hx').2 (hA hx).2
    have hfA : (A ∪ R).filter p = A := by
      ext x; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hp⟩
        · exact hx
        · exact absurd hp (hR hx).2
      · intro hx; exact ⟨Or.inl hx, (hA hx).2⟩
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_powersetCard, Finset.subset_iff,
      Finset.mem_union, hfA, hAc, and_true]
    refine ⟨?_, ?_⟩
    · rintro x (hx | hx)
      · exact (hA hx).1
      · exact (hR hx).1
    · rw [Finset.card_union_of_disjoint hdis, hAc, hRc]; omega
  · intro Q hQ
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_powersetCard] at hQ
    obtain ⟨⟨hQU, hQc⟩, hQm⟩ := hQ
    have := Finset.card_filter_add_card_filter_not (s := Q) p
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨⟨Finset.filter_subset_filter _ hQU, hQm⟩, Finset.filter_subset_filter _ hQU, ?_⟩
    omega
  · rintro ⟨A, R⟩ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powersetCard,
      Finset.subset_iff, Finset.mem_filter] at h
    obtain ⟨⟨hA, -⟩, ⟨hR, -⟩⟩ := h
    simp only [Prod.mk.injEq]
    constructor
    · ext x; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hp⟩
        · exact hx
        · exact absurd hp (hR hx).2
      · intro hx; exact ⟨Or.inl hx, (hA hx).2⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hp⟩
        · exact absurd (hA hx).2 hp
        · exact hx
      · intro hx; exact ⟨Or.inr hx, (hR hx).2⟩
  · intro Q _
    exact Finset.filter_union_filter_not_eq _ _

/-- The 4-subsets of `T` with no three points on a common side. -/
private noncomputable def good4 (T : Finset ℝ) : Finset (Finset ℝ) :=
  (((T.powersetCard 4).filter (fun Q => ¬ 3 ≤ (Q.filter S0).card)).filter
    (fun Q => ¬ 3 ≤ (Q.filter S1).card)).filter (fun Q => ¬ 3 ≤ (Q.filter S2).card)

/-- Pairs of chords `(w, y)`, `(x, z)` with `w < x < y < z`. -/
private noncomputable def crossH (T : Finset ℝ) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((Ch T) ×ˢ (Ch T)).filter (fun p => p.1.1 < p.2.1 ∧ p.2.1 < p.1.2 ∧ p.1.2 < p.2.2)

/-- Four sorted reals form a 4-set. -/
private lemma card_four {w x y z : ℝ} (h1 : w < x) (h2 : x < y) (h3 : y < z) :
    ({w, x, y, z} : Finset ℝ).card = 4 := by
  have hwx : w ≠ x := ne_of_lt h1
  have hwy : w ≠ y := ne_of_lt (h1.trans h2)
  have hwz : w ≠ z := ne_of_lt (h1.trans (h2.trans h3))
  have hxy : x ≠ y := ne_of_lt h2
  have hxz : x ≠ z := ne_of_lt (h2.trans h3)
  have hyz : y ≠ z := ne_of_lt h3
  simp [hwx, hwy, hwz, hxy, hxz, hyz]

/-- Crossing pairs of chords correspond to 4-subsets with no three points on a side. -/
private lemma crossH_card (T : Finset ℝ) (hT : ∀ t ∈ T, 0 ≤ t) :
    (crossH T).card = (good4 T).card := by
  classical
  apply Finset.card_nbij' (fun p => ({p.1.1, p.2.1, p.1.2, p.2.2} : Finset ℝ))
    (fun Q => if h : Q.card = 4 then ((Q.orderEmbOfFin h 0, Q.orderEmbOfFin h 2),
      (Q.orderEmbOfFin h 1, Q.orderEmbOfFin h 3)) else ((0, 0), (0, 0)))
  · rintro ⟨⟨w, y⟩, ⟨x, z⟩⟩ hp
    simp only [crossH, Finset.coe_filter, Finset.mem_product, mem_Ch,
      Set.mem_ofPred_eq] at hp
    obtain ⟨⟨⟨hw, hy, -, hwy⟩, ⟨hx, hz, -, hxz⟩⟩, h1, h2, h3⟩ := hp
    have hd := (diag_iff (hT w hw) h1 h2 h3).1 ⟨hwy, hxz⟩
    simp only [good4, Finset.coe_filter, Finset.mem_filter, Finset.mem_powersetCard,
      Set.mem_ofPred_eq]
    rw [three_le_card_filter _ h1 h2 h3, three_le_card_filter _ h1 h2 h3,
      three_le_card_filter _ h1 h2 h3, card_four h1 h2 h3]
    refine ⟨⟨⟨⟨?_, rfl⟩, hd.1⟩, hd.2.1⟩, hd.2.2⟩
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  · intro Q hQ
    simp only [good4, Finset.coe_filter, Finset.mem_filter, Finset.mem_powersetCard,
      Set.mem_ofPred_eq] at hQ
    obtain ⟨⟨⟨⟨hQU, hc⟩, g0⟩, g1⟩, g2⟩ := hQ
    simp only [hc, dite_true]
    set f := Q.orderEmbOfFin hc
    have m01 : f 0 < f 1 := f.strictMono (by decide)
    have m12 : f 1 < f 2 := f.strictMono (by decide)
    have m23 : f 2 < f 3 := f.strictMono (by decide)
    have hmem : ∀ i, f i ∈ T := fun i => hQU (Finset.orderEmbOfFin_mem Q hc i)
    have hQ : Q = {f 0, f 1, f 2, f 3} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem Q hc _
      · rw [hc, card_four m01 m12 m23]
    rw [hQ, three_le_card_filter _ m01 m12 m23] at g0 g1 g2
    have hd := (diag_iff (hT _ (hmem 0)) m01 m12 m23).2 ⟨g0, g1, g2⟩
    simp only [crossH, Finset.coe_filter, Finset.mem_product, mem_Ch, Set.mem_ofPred_eq]
    exact ⟨⟨⟨hmem 0, hmem 2, m01.trans m12, hd.1⟩, ⟨hmem 1, hmem 3, m12.trans m23, hd.2⟩⟩,
      m01, m12, m23⟩
  · rintro ⟨⟨w, y⟩, ⟨x, z⟩⟩ hp
    simp only [crossH, Finset.coe_filter, Finset.mem_product, mem_Ch,
      Set.mem_ofPred_eq] at hp
    obtain ⟨-, h1, h2, h3⟩ := hp
    have hc := card_four h1 h2 h3
    simp only [hc, dite_true]
    have hu := Finset.orderEmbOfFin_unique hc (f := ![w, x, y, z]) (by
      intro i; fin_cases i <;> simp) (by
      rw [Fin.strictMono_iff_lt_succ]
      intro i; fin_cases i <;> simp <;> linarith)
    rw [← hu]
    rfl
  · intro Q hQ
    simp only [good4, Finset.coe_filter, Finset.mem_filter, Finset.mem_powersetCard,
      Set.mem_ofPred_eq] at hQ
    obtain ⟨⟨⟨⟨hQU, hc⟩, -⟩, -⟩, -⟩ := hQ
    simp only [hc, dite_true]
    set f := Q.orderEmbOfFin hc
    have m01 : f 0 < f 1 := f.strictMono (by decide)
    have m12 : f 1 < f 2 := f.strictMono (by decide)
    have m23 : f 2 < f 3 := f.strictMono (by decide)
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem Q hc _
    · rw [hc, card_four m01 m12 m23]

/-- The number of 4-subsets with at least three points on a set of `n + 2` points. -/
private lemma bad_card (n : ℕ) (U : Finset ℝ) (hU : U.card = 3 * n + 3) (p : ℝ → Prop)
    [DecidablePred p] (hp : (U.filter p).card = n + 2) :
    ((U.powersetCard 4).filter (fun Q => 3 ≤ (Q.filter p).card)).card
      = (n + 2).choose 3 * (2 * n + 1) + (n + 2).choose 4 := by
  have hnp : (U.filter (fun x => ¬ p x)).card = 2 * n + 1 := by
    have := Finset.card_filter_add_card_filter_not (s := U) p
    rw [hU, hp] at this
    omega
  have e : (U.powersetCard 4).filter (fun Q => 3 ≤ (Q.filter p).card) =
      ((U.powersetCard 4).filter (fun Q => (Q.filter p).card = 3)) ∪
      ((U.powersetCard 4).filter (fun Q => (Q.filter p).card = 4)) := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have : (Q.filter p).card ≤ 4 := h2 ▸ Finset.card_filter_le _ _
      refine (show (Q.filter p).card = 3 ∨ (Q.filter p).card = 4 by omega).imp ?_ ?_ <;>
        exact fun h => ⟨⟨h1, h2⟩, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
  rw [e, Finset.card_union_of_disjoint, card_filter_card_eq _ _ _ _ (by norm_num),
    card_filter_card_eq _ _ _ _ (by norm_num), hp, hnp]
  · simp
  · rw [Finset.disjoint_left]
    intro Q h1 h2
    simp only [Finset.mem_filter] at h1 h2
    omega

/-- A 4-set cannot have three points on each of two sides. -/
private lemma not_both_bad {Q : Finset ℝ} (hQ : Q.card = 4) (p q : ℝ → Prop) [DecidablePred p]
    [DecidablePred q] (c : ℝ) (hpq : ∀ x, p x → q x → x = c) :
    ¬ (3 ≤ (Q.filter p).card ∧ 3 ≤ (Q.filter q).card) := by
  rintro ⟨h1, h2⟩
  have hu : (Q.filter p ∪ Q.filter q).card ≤ 4 :=
    hQ ▸ Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))
  have hi : (Q.filter p ∩ Q.filter q).card ≤ 1 := by
    calc (Q.filter p ∩ Q.filter q).card ≤ ({c} : Finset ℝ).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_filter] at hx
          simp [hpq x hx.1.2 hx.2.2]
      _ = 1 := Finset.card_singleton c
  have := Finset.card_union_add_card_inter (Q.filter p) (Q.filter q)
  omega

/-- Inclusion-exclusion for the 4-subsets with no three points on a side. -/
private lemma good4_card (n : ℕ) (T : Finset ℝ) (hN : T.card = 3 * n + 3)
    (c0 : (T.filter S0).card = n + 2) (c1 : (T.filter S1).card = n + 2)
    (c2 : (T.filter S2).card = n + 2) :
    (good4 T).card + 3 * ((n + 2).choose 3 * (2 * n + 1) + (n + 2).choose 4) =
      (3 * n + 3).choose 4 := by
  have b0 := bad_card n T hN S0 c0
  have b1 := bad_card n T hN S1 c1
  have b2 := bad_card n T hN S2 c2
  set P4 := T.powersetCard 4
  have t0 := Finset.card_filter_add_card_filter_not (s := P4)
    (fun Q => 3 ≤ (Q.filter S0).card)
  have t1 := Finset.card_filter_add_card_filter_not
    (s := P4.filter (fun Q => ¬ 3 ≤ (Q.filter S0).card)) (fun Q => 3 ≤ (Q.filter S1).card)
  have t2 := Finset.card_filter_add_card_filter_not
    (s := (P4.filter (fun Q => ¬ 3 ≤ (Q.filter S0).card)).filter
      (fun Q => ¬ 3 ≤ (Q.filter S1).card)) (fun Q => 3 ≤ (Q.filter S2).card)
  have e1 : (P4.filter (fun Q => ¬ 3 ≤ (Q.filter S0).card)).filter
      (fun Q => 3 ≤ (Q.filter S1).card) = P4.filter (fun Q => 3 ≤ (Q.filter S1).card) := by
    ext Q
    simp only [Finset.mem_filter, P4, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      refine ⟨⟨h, fun h0 => not_both_bad h.2 S0 S1 1
        (fun x a b => by unfold S0 at a; unfold S1 at b; linarith [b.1]) ⟨h0, h'⟩⟩, h'⟩
  have e2 : ((P4.filter (fun Q => ¬ 3 ≤ (Q.filter S0).card)).filter
      (fun Q => ¬ 3 ≤ (Q.filter S1).card)).filter (fun Q => 3 ≤ (Q.filter S2).card) =
      P4.filter (fun Q => 3 ≤ (Q.filter S2).card) := by
    ext Q
    simp only [Finset.mem_filter, P4, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨⟨h, -⟩, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      refine ⟨⟨⟨h, fun h0 => not_both_bad h.2 S0 S2 0
        (fun x a b => by
          unfold S0 at a; unfold S2 at b
          rcases b with b | b
          · linarith
          · exact b) ⟨h0, h'⟩⟩,
        fun h1 => not_both_bad h.2 S1 S2 2
        (fun x a b => by
          unfold S1 at a; unfold S2 at b
          rcases b with b | b
          · linarith [a.2]
          · linarith [a.1]) ⟨h1, h'⟩⟩, h'⟩
  rw [e1] at t1
  rw [e2] at t2
  have hP4 : P4.card = (3 * n + 3).choose 4 := by
    simp only [P4, Finset.card_powersetCard, hN]
  have : good4 T = ((P4.filter (fun Q => ¬ 3 ≤ (Q.filter S0).card)).filter
      (fun Q => ¬ 3 ≤ (Q.filter S1).card)).filter (fun Q => ¬ 3 ≤ (Q.filter S2).card) :=
    rfl
  rw [this]
  omega

/-- The total number of crossings, counted from both chords, is twice the number of crossing
pairs. -/
private lemma sum_crossers (T : Finset ℝ) :
    ∑ c ∈ Ch T, ((Ch T).filter (fun d => crossR c d)).card = 2 * (crossH T).card := by
  classical
  have h1 : ∑ c ∈ Ch T, ((Ch T).filter (fun d => crossR c d)).card =
      ((Ch T ×ˢ Ch T).filter (fun p => crossR p.1 p.2)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.card_filter]
  have h2 : (Ch T ×ˢ Ch T).filter (fun p => crossR p.1 p.2) =
      crossH T ∪ (crossH T).image Prod.swap := by
    ext ⟨c, d⟩
    simp only [crossH, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
      Finset.mem_product, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    unfold crossR
    constructor
    · rintro ⟨⟨hc, hd⟩, h | h⟩
      · exact Or.inl ⟨⟨hc, hd⟩, h⟩
      · exact Or.inr ⟨d.1, d.2, c.1, c.2, ⟨⟨hd, hc⟩, h⟩, rfl, rfl⟩
    · rintro (⟨⟨hc, hd⟩, h⟩ | ⟨a, b, a', b', ⟨⟨h1, h2⟩, h⟩, rfl, rfl⟩)
      · exact ⟨⟨hc, hd⟩, Or.inl h⟩
      · exact ⟨⟨h2, h1⟩, Or.inr h⟩
  rw [h1, h2, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ Prod.swap_injective]
  · ring
  · rw [Finset.disjoint_left]
    rintro ⟨c, d⟩ h h'
    simp only [crossH, Finset.mem_filter, Finset.mem_image, Prod.exists, Prod.swap_prod_mk,
      Prod.mk.injEq] at h h'
    obtain ⟨a, b, a', b', ⟨-, h3⟩, rfl, rfl⟩ := h'
    obtain ⟨-, h4⟩ := h
    simp only at h3 h4
    linarith [h3.1, h3.2.1, h4.1, h4.2.1]

/-- `m choose 2` as a rational polynomial. -/
private lemma cast_choose_two (m : ℕ) : ((m.choose 2 : ℕ) : ℚ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; rw [ih]; ring

/-- `m choose 3` as a rational polynomial. -/
private lemma cast_choose_three (m : ℕ) : ((m.choose 3 : ℕ) : ℚ) = m * (m - 1) * (m - 2) / 6 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ]; push_cast; rw [ih, cast_choose_two]; ring

/-- `m choose 4` as a rational polynomial. -/
private lemma cast_choose_four (m : ℕ) :
    ((m.choose 4 : ℕ) : ℚ) = m * (m - 1) * (m - 2) * (m - 3) / 24 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ]; push_cast; rw [ih, cast_choose_three]; ring

/-- The total number of crossings on the chords. -/
private lemma crossings_formula (n : ℕ) (T : Finset ℝ) (hT : ∀ t ∈ T, 0 ≤ t)
    (hN : T.card = 3 * n + 3)
    (c0 : (T.filter S0).card = n + 2) (c1 : (T.filter S1).card = n + 2)
    (c2 : (T.filter S2).card = n + 2) :
    ((∑ c ∈ Ch T, ((Ch T).filter (fun d => crossR c d)).card : ℕ) : ℚ) =
      3 / 2 * n ^ 2 * (n + 1) * (3 * n + 1) := by
  rw [sum_crossers, crossH_card T hT]
  have h := good4_card n T hN c0 c1 c2
  have h' : ((good4 T).card : ℚ) = ((3 * n + 3).choose 4 : ℕ) -
      3 * (((n + 2).choose 3 : ℕ) * (2 * n + 1) + ((n + 2).choose 4 : ℕ)) := by
    rw [← h]; push_cast; ring
  push_cast
  rw [h', cast_choose_four, cast_choose_four, cast_choose_three]
  push_cast
  ring

/-! ### Number of chords -/

/-- The number of chords is `3n(n+1)`. -/
private lemma chords_card (n : ℕ) (T : Finset ℝ) (hN : T.card = 3 * n + 3)
    (c0 : (T.filter S0).card = n + 2) (c1 : (T.filter S1).card = n + 2)
    (c2 : (T.filter S2).card = n + 2) :
    ((Ch T).card : ℚ) = 3 * n * (n + 1) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := T.offDiag)
    (fun p => coSide p.1 p.2)
  have hnot : T.offDiag.filter (fun p => ¬ coSide p.1 p.2) = Ch T ∪ (Ch T).image Prod.swap := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_union, Finset.mem_image,
      mem_Ch, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb, hab⟩, hc⟩
      rcases lt_or_gt_of_ne hab with h | h
      · exact Or.inl ⟨ha, hb, h, hc⟩
      · refine Or.inr ⟨b, a, ⟨hb, ha, h, fun h' => hc ?_⟩, rfl, rfl⟩
        unfold coSide at h' ⊢; tauto
    · rintro (⟨ha, hb, h, hc⟩ | ⟨x, y, ⟨hx, hy, h, hc⟩, rfl, rfl⟩)
      · exact ⟨⟨ha, hb, ne_of_lt h⟩, hc⟩
      · refine ⟨⟨hy, hx, ne_of_gt h⟩, fun h' => hc ?_⟩
        unfold coSide at h' ⊢; tauto
  have hdis : Disjoint (Ch T) ((Ch T).image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h h'
    simp only [Finset.mem_image, mem_Ch, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq] at h h'
    obtain ⟨x, y, ⟨-, -, hxy, -⟩, rfl, rfl⟩ := h'
    exact lt_asymm h.2.2.1 hxy
  have hyes : T.offDiag.filter (fun p => coSide p.1 p.2) =
      ((T.filter S0).offDiag ∪ (T.filter S1).offDiag) ∪ (T.filter S2).offDiag := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_union]
    unfold coSide
    tauto
  have d01 : Disjoint (T.filter S0).offDiag (T.filter S1).offDiag := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h h'
    simp only [Finset.mem_offDiag, Finset.mem_filter, S0, S1] at h h'
    exact h.2.2 (by linarith [h.1.2, h.2.1.2, h'.1.2.1, h'.2.1.2.1])
  have d2 : Disjoint ((T.filter S0).offDiag ∪ (T.filter S1).offDiag) (T.filter S2).offDiag := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h h'
    simp only [Finset.mem_union, Finset.mem_offDiag, Finset.mem_filter, S0, S1, S2] at h h'
    obtain ⟨⟨-, ha⟩, ⟨-, hb⟩, hab⟩ := h'
    rcases h with ⟨⟨-, ha'⟩, ⟨-, hb'⟩, -⟩ | ⟨⟨-, ha'⟩, ⟨-, hb'⟩, -⟩
    · apply hab
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · linarith
      · linarith
      · linarith
      · rw [ha, hb]
    · apply hab
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · linarith [ha'.2, hb'.2]
      · linarith [hb'.1]
      · linarith [ha'.1]
      · rw [ha, hb]
  rw [hnot, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ Prod.swap_injective, hyes,
    Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d01,
    Finset.offDiag_card, Finset.offDiag_card, Finset.offDiag_card, Finset.offDiag_card,
    c0, c1, c2, hN] at hsplit
  have k1 : (n + 2) ≤ (n + 2) * (n + 2) := Nat.le_mul_self _
  have k2 : (3 * n + 3) ≤ (3 * n + 3) * (3 * n + 3) := Nat.le_mul_self _
  have hq : ((((n + 2) * (n + 2) - (n + 2) + ((n + 2) * (n + 2) - (n + 2)) +
      ((n + 2) * (n + 2) - (n + 2)) + ((Ch T).card + (Ch T).card)) : ℕ) : ℚ) =
      (((3 * n + 3) * (3 * n + 3) - (3 * n + 3) : ℕ) : ℚ) := by rw [hsplit]
  push_cast [Nat.cast_sub k1, Nat.cast_sub k2] at hq
  linarith

/-- `√3 * √3 = 3`. -/
private lemma sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- `D a b` is continuous. -/
private lemma continuous_D (a b : ℂ) : Continuous fun z => D a b z := by
  unfold D; fun_prop

/-- A point on the inner side of all three side lines lies in the triangle. -/
private lemma mem_triangle_of {z : ℂ} (h0 : 0 ≤ D (corner 0) (corner 1) z)
    (h1 : 0 ≤ D (corner 1) (corner 2) z) (h2 : 0 ≤ D (corner 2) (corner 0) z) :
    z ∈ triangle := by
  have hs := sqrt3_pos
  have hs2 := sqrt3_sq
  let w : Fin 3 → ℝ := ![D (corner 1) (corner 2) z / (Real.sqrt 3 / 2),
    D (corner 2) (corner 0) z / (Real.sqrt 3 / 2), D (corner 0) (corner 1) z / (Real.sqrt 3 / 2)]
  have key := (convex_convexHull ℝ (Set.range corner)).sum_mem (t := Finset.univ) (w := w)
    (z := corner) ?_ ?_ ?_
  · unfold triangle
    convert key using 1
    simp only [Fin.sum_univ_three, w, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, corner_zero, corner_one, corner_two]
    apply Complex.ext <;>
    · simp only [D, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
        Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im, Complex.one_re,
        Complex.one_im, smul_eq_mul]
      field_simp
      ring
  · intro i _
    have h3 : 0 < Real.sqrt 3 / 2 := by positivity
    fin_cases i
    · exact div_nonneg h1 h3.le
    · exact div_nonneg h2 h3.le
    · exact div_nonneg h0 h3.le
  · simp only [Fin.sum_univ_three, w, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, corner_zero, corner_one,
      corner_two, D, Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im]
    field_simp
    ring
  · intro i _
    exact subset_convexHull ℝ _ (Set.mem_range_self i)

/-- A point strictly on the inner side of all three side lines lies in the interior. -/
private lemma mem_interior_of {z : ℂ} (h0 : 0 < D (corner 0) (corner 1) z)
    (h1 : 0 < D (corner 1) (corner 2) z) (h2 : 0 < D (corner 2) (corner 0) z) :
    z ∈ interior triangle := by
  let U : Set ℂ := {w | 0 < D (corner 0) (corner 1) w ∧ 0 < D (corner 1) (corner 2) w ∧
    0 < D (corner 2) (corner 0) w}
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_lt continuous_const (continuous_D _ _)) ?_
    exact IsOpen.inter (isOpen_lt continuous_const (continuous_D _ _))
      (isOpen_lt continuous_const (continuous_D _ _))
  have hsub : U ⊆ triangle := fun w hw => mem_triangle_of hw.1.le hw.2.1.le hw.2.2.le
  exact interior_maximal hsub hU ⟨h0, h1, h2⟩

/-! ### Signs -/

/-- The sign of `D` at boundary points is the sign of `E`. -/
private lemma D_pos_of {a b c : ℝ} (h : 0 < E a b c) : 0 < D (P a) (P b) (P c) := by
  rw [D_P]; exact mul_pos sqrt3_pos h

/-- The sign of `D` at boundary points is the sign of `E`. -/
private lemma D_neg_of {a b c : ℝ} (h : E a b c < 0) : D (P a) (P b) (P c) < 0 := by
  rw [D_P]; exact mul_neg_of_pos_of_neg sqrt3_pos h

/-- A triple containing a chord is not on a common side. -/
private lemma not_coSide3_of {a b x y z : ℝ} (hc : ¬ coSide a b)
    (h : ∀ p : ℝ → Prop, p x ∧ p y ∧ p z → p a ∧ p b) : ¬ coSide3 x y z := by
  unfold coSide3; unfold coSide at hc
  rintro (h' | h' | h')
  · exact hc (Or.inl (h S0 h'))
  · exact hc (Or.inr (Or.inl (h S1 h')))
  · exact hc (Or.inr (Or.inr (h S2 h')))

/-- The sign of `E a b t` for a chord `(a, b)` and another boundary parameter `t`. -/
private lemma E_sign {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 3) (hc : ¬ coSide a b)
    (ht0 : 0 ≤ t) (ht3 : t < 3) :
    (a < t → t < b → E a b t < 0) ∧ (t < a → 0 < E a b t) ∧ (b < t → 0 < E a b t) := by
  refine ⟨fun h1 h2 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · have := E_pos ha h1 h2 hb (not_coSide3_of hc (fun p h => ⟨h.1, h.2.2⟩))
    rw [E_swap]; linarith
  · have := E_pos ht0 h1 hab hb (not_coSide3_of hc (fun p h => ⟨h.2.1, h.2.2⟩))
    rw [← E_cyc]; exact this
  · exact E_pos ha hab h1 ht3 (not_coSide3_of hc (fun p h => ⟨h.1, h.2.1⟩))

/-- No other boundary point lies on the line of a chord. -/
private lemma E_ne {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 3) (hc : ¬ coSide a b)
    (ht0 : 0 ≤ t) (ht3 : t < 3) (hta : t ≠ a) (htb : t ≠ b) : E a b t ≠ 0 := by
  obtain ⟨s1, s2, s3⟩ := E_sign ha hab hb hc ht0 ht3
  rcases lt_or_gt_of_ne hta with h | h
  · exact (s2 h).ne'
  · rcases lt_or_gt_of_ne htb with h' | h'
    · exact (s1 h h').ne
    · exact (s3 h').ne'

/-- No other boundary point lies on the line of a chord. -/
private lemma D_ne {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 3) (hc : ¬ coSide a b)
    (ht0 : 0 ≤ t) (ht3 : t < 3) (hta : t ≠ a) (htb : t ≠ b) : D (P a) (P b) (P t) ≠ 0 := by
  rw [D_P]; exact mul_ne_zero sqrt3_pos.ne' (E_ne ha hab hb hc ht0 ht3 hta htb)

/-! ### Chords -/

/-- The drawn segment of a pair of parameters. -/
private def seg (c : ℝ × ℝ) : Set ℂ := segment ℝ (P c.1) (P c.2)

/-- The relative interior of the drawn segment of a pair of parameters. -/
private def oseg (c : ℝ × ℝ) : Set ℂ := openSegment ℝ (P c.1) (P c.2)

/-- The crossing point of two chords. -/
private noncomputable def X (c d : ℝ × ℝ) : ℂ := crossPt (P c.1) (P c.2) (P d.1) (P d.2)

/-- Standing hypothesis: all parameters lie in `[0, 3)`. -/
private def Good (T : Finset ℝ) : Prop := ∀ t ∈ T, 0 ≤ t ∧ t < 3

section
variable {T : Finset ℝ} (hT : Good T)
include hT

/-- `P` is injective on `T`. -/
private lemma P_injT {s t : ℝ} (hs : s ∈ T) (ht : t ∈ T) (h : P s = P t) : s = t :=
  P_inj (hT s hs).1 (hT s hs).2 (hT t ht).1 (hT t ht).2 h

/-- Distinct parameters of `T` give distinct points. -/
private lemma P_ne_of_ne {s t : ℝ} (hs : s ∈ T) (ht : t ∈ T) (h : s ≠ t) : P s ≠ P t :=
  fun e => h (P_injT hT hs ht e)

/-- The relative interior of a chord is strictly inside all three side lines. -/
private lemma oseg_pos {c : ℝ × ℝ} (hc : c ∈ Ch T) {z : ℂ} (hz : z ∈ oseg c) (j : Fin 3) :
    0 < D (corner j) (corner (j + 1)) z := by
  rw [mem_Ch] at hc
  obtain ⟨ha, hb, -, hco⟩ := hc
  have ha' := hT _ ha
  have hb' := hT _ hb
  apply openSeg_pos (Dline_nonneg j ha'.1 ha'.2) (Dline_nonneg j hb'.1 hb'.2) _ hz
  rw [Dline_pos_iff j ha'.1 ha'.2, Dline_pos_iff j hb'.1 hb'.2]
  by_contra h
  push Not at h
  exact hco ((coSide_iff _ _).2 ⟨j, h⟩)

/-- The relative interior of a chord lies in the interior of the triangle. -/
private lemma oseg_interior {c : ℝ × ℝ} (hc : c ∈ Ch T) {z : ℂ} (hz : z ∈ oseg c) :
    z ∈ interior triangle :=
  mem_interior_of (oseg_pos hT hc hz 0) (oseg_pos hT hc hz 1) (oseg_pos hT hc hz 2)

/-- The relative interior of a chord avoids the sides. -/
private lemma oseg_not_side {c : ℝ × ℝ} (hc : c ∈ Ch T) {z : ℂ} (hz : z ∈ oseg c) (j : Fin 3) :
    z ∉ side j := by
  intro h
  have := oseg_pos hT hc hz j
  rw [Dline_zero_of_mem_side j h] at this
  exact lt_irrefl _ this

/-- The endpoints of a chord are distinct. -/
private lemma chord_ne {c : ℝ × ℝ} (hc : c ∈ Ch T) : P c.1 ≠ P c.2 := by
  rw [mem_Ch] at hc
  exact P_ne_of_ne hT hc.1 hc.2.1 (ne_of_lt hc.2.2.1)

omit hT in
/-- A point of a chord other than its endpoints is in its relative interior. -/
private lemma mem_oseg_of {c : ℝ × ℝ} (_hc : c ∈ Ch T) {z : ℂ} (hz : z ∈ seg c) (h1 : z ≠ P c.1)
    (h2 : z ≠ P c.2) : z ∈ oseg c := by
  unfold seg at hz
  rw [← insert_endpoints_openSegment] at hz
  rcases hz with hz | hz | hz
  · exact absurd hz h1
  · exact absurd hz h2
  · exact hz

/-- The endpoints of a chord are not in its relative interior. -/
private lemma endpoint_not_oseg {c : ℝ × ℝ} (hc : c ∈ Ch T) : P c.1 ∉ oseg c ∧ P c.2 ∉ oseg c := by
  have hne := chord_ne hT hc
  unfold oseg
  rw [left_mem_openSegment_iff, right_mem_openSegment_iff]
  exact ⟨hne, hne⟩

/-- A boundary point other than the endpoints is not on a chord. -/
private lemma P_not_mem_seg {c : ℝ × ℝ} (hc : c ∈ Ch T) {t : ℝ} (ht : t ∈ T) (h1 : t ≠ c.1)
    (h2 : t ≠ c.2) : P t ∉ seg c := by
  intro h
  rw [mem_Ch] at hc
  have := D_ne (hT _ hc.1).1 hc.2.2.1 (hT _ hc.2.1).2 hc.2.2.2 (hT t ht).1 (hT t ht).2 h1 h2
  exact this (D_of_mem_segment h)

/-- Two chords with interleaving endpoints cross at `X c d`. -/
private lemma X_mem {c d : ℝ × ℝ} (hc : c ∈ Ch T) (hd : d ∈ Ch T) (h : crossR c d) :
    X c d ∈ oseg c ∧ X c d ∈ oseg d := by
  rw [mem_Ch] at hc hd
  obtain ⟨ha, hb, hab, hcab⟩ := hc
  obtain ⟨he, hf, hef, hcef⟩ := hd
  obtain ⟨ha0, ha3⟩ := hT _ ha
  obtain ⟨hb0, hb3⟩ := hT _ hb
  obtain ⟨he0, he3⟩ := hT _ he
  obtain ⟨hf0, hf3⟩ := hT _ hf
  have sab_e := E_sign ha0 hab hb3 hcab he0 he3
  have sab_f := E_sign ha0 hab hb3 hcab hf0 hf3
  have sef_a := E_sign he0 hef hf3 hcef ha0 ha3
  have sef_b := E_sign he0 hef hf3 hcef hb0 hb3
  unfold crossR at h
  apply crossPt_mem
  · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact mul_neg_of_neg_of_pos (D_neg_of (sab_e.1 h1 (by linarith)))
        (D_pos_of (sab_f.2.2 (by linarith)))
    · exact mul_neg_of_pos_of_neg (D_pos_of (sab_e.2.1 h1))
        (D_neg_of (sab_f.1 (by linarith) (by linarith)))
  · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact mul_neg_of_pos_of_neg (D_pos_of (sef_a.2.1 h1))
        (D_neg_of (sef_b.1 (by linarith) (by linarith)))
    · exact mul_neg_of_neg_of_pos (D_neg_of (sef_a.1 h1 (by linarith)))
        (D_pos_of (sef_b.2.2 (by linarith)))

/-- Distinct chords meet in at most one point. -/
private lemma seg_inter_unique {c d : ℝ × ℝ} (hc : c ∈ Ch T) (hd : d ∈ Ch T) (hcd : c ≠ d)
    {u v : ℂ} (hu : u ∈ seg c) (hu' : u ∈ seg d) (hv : v ∈ seg c) (hv' : v ∈ seg d) :
    u = v := by
  have hc' := hc
  rw [mem_Ch] at hc' hd
  obtain ⟨ha, hb, hab, hcab⟩ := hc'
  obtain ⟨he, hf, hef, -⟩ := hd
  obtain ⟨ha0, ha3⟩ := hT _ ha
  by_cases h1 : d.1 = c.1 ∨ d.1 = c.2
  · have h2 : d.2 ≠ c.1 ∧ d.2 ≠ c.2 := by
      constructor
      · intro e; rcases h1 with h1 | h1 <;> linarith
      · intro e
        rcases h1 with h1 | h1
        · exact hcd (Prod.ext h1.symm e.symm)
        · linarith
    have hD := D_ne ha0 hab (hT _ hb).2 hcab (hT _ hf).1 (hT _ hf).2 h2.1 h2.2
    unfold seg at hu hu' hv hv'
    rw [segment_symm] at hu' hv'
    exact seg_inter_sub hD hu hu' hv hv'
  · push Not at h1
    have hD := D_ne ha0 hab (hT _ hb).2 hcab (hT _ he).1 (hT _ he).2 h1.1 h1.2
    exact seg_inter_sub hD hu hu' hv hv'

/-- Two crossing chords meet exactly at `X c d`. -/
private lemma seg_inter_X {c d : ℝ × ℝ} (hc : c ∈ Ch T) (hd : d ∈ Ch T) (h : crossR c d) :
    seg c ∩ seg d = {X c d} := by
  have hX := X_mem hT hc hd h
  have hcd : c ≠ d := by
    rintro rfl; unfold crossR at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> exact lt_irrefl _ h1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact seg_inter_unique hT hc hd hcd h1 h2 (openSegment_subset_segment _ _ _ hX.1)
      (openSegment_subset_segment _ _ _ hX.2)
  · rintro rfl
    exact ⟨openSegment_subset_segment _ _ _ hX.1, openSegment_subset_segment _ _ _ hX.2⟩

/-- Two distinct chords meeting at a point of the relative interior of one of them cross. -/
private lemma crossR_of_mem {c d : ℝ × ℝ} (hc : c ∈ Ch T) (hd : d ∈ Ch T) (hcd : c ≠ d) {z : ℂ}
    (hz : z ∈ oseg c) (hz' : z ∈ seg d) : crossR c d := by
  by_contra hn
  have hc' := hc
  have hd' := hd
  rw [mem_Ch] at hc' hd'
  obtain ⟨ha, hb, hab, hcab⟩ := hc'
  obtain ⟨he, hf, hef, hcef⟩ := hd'
  obtain ⟨ha0, ha3⟩ := hT _ ha
  obtain ⟨hb0, hb3⟩ := hT _ hb
  obtain ⟨he0, he3⟩ := hT _ he
  obtain ⟨hf0, hf3⟩ := hT _ hf
  have hz0 : D (P c.1) (P c.2) z = 0 := D_of_mem_segment (openSegment_subset_segment _ _ _ hz)
  have hne := endpoint_not_oseg hT hc
  unfold crossR at hn
  push Not at hn
  by_cases hsh : d.1 = c.1 ∨ d.1 = c.2 ∨ d.2 = c.1 ∨ d.2 = c.2
  · -- a shared endpoint
    have hzc : z ∈ seg c := openSegment_subset_segment _ _ _ hz
    have hPa : P c.1 ∈ seg c := left_mem_segment _ _ _
    have hPb : P c.2 ∈ seg c := right_mem_segment _ _ _
    unfold seg at hz' hzc hPa hPb
    rcases hsh with h | h | h | h
    · have hf1 : d.2 ≠ c.1 := by intro e; linarith
      have hf2 : d.2 ≠ c.2 := fun e => hcd (Prod.ext h.symm e.symm)
      have hD := D_ne ha0 hab hb3 hcab hf0 hf3 hf1 hf2
      rw [segment_symm, h] at hz'
      have e := seg_inter_sub hD hzc hz' hPa (right_mem_segment _ _ _)
      rw [e] at hz; exact hne.1 hz
    · have hf1 : d.2 ≠ c.1 := by intro e; linarith
      have hf2 : d.2 ≠ c.2 := by intro e; linarith
      have hD := D_ne ha0 hab hb3 hcab hf0 hf3 hf1 hf2
      rw [segment_symm, h] at hz'
      have e := seg_inter_sub hD hzc hz' hPb (right_mem_segment _ _ _)
      rw [e] at hz; exact hne.2 hz
    · have he1 : d.1 ≠ c.1 := by intro e; linarith
      have he2 : d.1 ≠ c.2 := by intro e; linarith
      have hD := D_ne ha0 hab hb3 hcab he0 he3 he1 he2
      rw [h] at hz'
      have e := seg_inter_sub hD hzc hz' hPa (right_mem_segment _ _ _)
      rw [e] at hz; exact hne.1 hz
    · have he1 : d.1 ≠ c.1 := fun e => hcd (Prod.ext e.symm h.symm)
      have he2 : d.1 ≠ c.2 := by intro e; linarith
      have hD := D_ne ha0 hab hb3 hcab he0 he3 he1 he2
      rw [h] at hz'
      have e := seg_inter_sub hD hzc hz' hPb (right_mem_segment _ _ _)
      rw [e] at hz; exact hne.2 hz
  · push Not at hsh
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    obtain ⟨s1, s2, s3⟩ := E_sign ha0 hab hb3 hcab he0 he3
    obtain ⟨t1, t2, t3⟩ := E_sign ha0 hab hb3 hcab hf0 hf3
    have key : (0 < D (P c.1) (P c.2) (P d.1) ∧ 0 < D (P c.1) (P c.2) (P d.2)) ∨
        (D (P c.1) (P c.2) (P d.1) < 0 ∧ D (P c.1) (P c.2) (P d.2) < 0) := by
      rcases lt_or_gt_of_ne h1 with e1 | e1
      · -- d.1 < c.1
        rcases lt_or_gt_of_ne h4 with e4 | e4
        · rcases lt_or_gt_of_ne h3 with e3 | e3
          · exact Or.inl ⟨D_pos_of (s2 e1), D_pos_of (t2 e3)⟩
          · exact absurd (hn.2 e1 e3) (not_le.2 e4)
        · exact Or.inl ⟨D_pos_of (s2 e1), D_pos_of (t3 e4)⟩
      · rcases lt_or_gt_of_ne h2 with e2 | e2
        · rcases lt_or_gt_of_ne h4 with e4 | e4
          · exact Or.inr ⟨D_neg_of (s1 e1 e2), D_neg_of (t1 (by linarith) e4)⟩
          · exact absurd (hn.1 e1 e2) (not_le.2 e4)
        · exact Or.inl ⟨D_pos_of (s3 e2), D_pos_of (t3 (by linarith))⟩
    rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · have := seg_pos k1 k2 hz'
      rw [hz0] at this; exact lt_irrefl _ this
    · have := seg_neg k1 k2 hz'
      rw [hz0] at this; exact lt_irrefl _ this

end

/-! ### A one-dimensional lemma -/

/-- Two segments on a common line whose relative interiors share a point share a second
point. -/
private lemma oneD {p q x y u v z : ℂ} (hpq : p ≠ q) (hx : x ∈ segment ℝ p q)
    (hy : y ∈ segment ℝ p q)
    (hu : u ∈ segment ℝ p q) (hv : v ∈ segment ℝ p q) (hxy : x ≠ y) (huv : u ≠ v)
    (hz1 : z ∈ openSegment ℝ x y) (hz2 : z ∈ openSegment ℝ u v) :
    ∃ w, w ≠ z ∧ w ∈ segment ℝ x y ∧ w ∈ segment ℝ u v := by
  set L : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap p q
  have hL : Function.Injective L := AffineMap.lineMap_injective ℝ hpq
  rw [segment_eq_image_lineMap] at hx hy hu hv
  obtain ⟨α, -, rfl⟩ := hx
  obtain ⟨β, -, rfl⟩ := hy
  obtain ⟨γ, -, rfl⟩ := hu
  obtain ⟨δ, -, rfl⟩ := hv
  have hαβ : α ≠ β := fun h => hxy (by rw [h])
  have hγδ : γ ≠ δ := fun h => huv (by rw [h])
  rw [← image_openSegment] at hz1 hz2
  obtain ⟨ζ, hζ, rfl⟩ := hz1
  obtain ⟨ζ', hζ', hζζ⟩ := hz2
  have e := hL hζζ
  rw [e] at hζ'
  rw [openSegment_eq_Ioo' hαβ] at hζ
  rw [openSegment_eq_Ioo' hγδ] at hζ'
  set m := min (max α β) (max γ δ)
  have hm1 : m ≤ max α β := min_le_left _ _
  have hm2 : m ≤ max γ δ := min_le_right _ _
  have hζm : ζ < m := lt_min hζ.2 hζ'.2
  refine ⟨L ((ζ + m) / 2), fun h => ?_, ?_, ?_⟩
  · have := hL h; linarith
  · rw [← image_segment, segment_eq_uIcc]
    refine ⟨(ζ + m) / 2, ?_, rfl⟩
    rw [Set.mem_uIcc]
    rcases le_total α β with h | h
    · left
      rw [min_eq_left h] at hζ; rw [max_eq_right h] at hζ hm1
      constructor <;> linarith [hζ.1]
    · right
      rw [min_eq_right h] at hζ; rw [max_eq_left h] at hζ hm1
      constructor <;> linarith [hζ.1]
  · rw [← image_segment, segment_eq_uIcc]
    refine ⟨(ζ + m) / 2, ?_, rfl⟩
    rw [Set.mem_uIcc]
    rcases le_total γ δ with h | h
    · left
      rw [min_eq_left h] at hζ'; rw [max_eq_right h] at hζ' hm2
      constructor <;> linarith [hζ'.1]
    · right
      rw [min_eq_right h] at hζ'; rw [max_eq_left h] at hζ' hm2
      constructor <;> linarith [hζ'.1]

/-! ### Sides meet only at corners -/

/-- Two distinct sides share exactly one parameter, a corner. -/
private lemma Sd_inter {j j' : Fin 3} (hjj : j ≠ j') :
    ∃ c : ℝ, (c = 0 ∨ c = 1 ∨ c = 2) ∧ ∀ t, Sd j t → Sd j' t → t = c := by
  fin_cases j <;> fin_cases j'
  · exact absurd rfl hjj
  · refine ⟨1, Or.inr (Or.inl rfl), fun t h h' => ?_⟩
    change t ≤ 1 at h; change 1 ≤ t ∧ t ≤ 2 at h'; linarith [h'.1]
  · refine ⟨0, Or.inl rfl, fun t h h' => ?_⟩
    change t ≤ 1 at h; change 2 ≤ t ∨ t = 0 at h'
    rcases h' with h' | h'
    · linarith
    · exact h'
  · refine ⟨1, Or.inr (Or.inl rfl), fun t h h' => ?_⟩
    change 1 ≤ t ∧ t ≤ 2 at h; change t ≤ 1 at h'; linarith [h.1]
  · exact absurd rfl hjj
  · refine ⟨2, Or.inr (Or.inr rfl), fun t h h' => ?_⟩
    change 1 ≤ t ∧ t ≤ 2 at h; change 2 ≤ t ∨ t = 0 at h'
    rcases h' with h' | h'
    · linarith [h.2]
    · linarith [h.1]
  · refine ⟨0, Or.inl rfl, fun t h h' => ?_⟩
    change 2 ≤ t ∨ t = 0 at h; change t ≤ 1 at h'
    rcases h with h | h
    · linarith
    · exact h
  · refine ⟨2, Or.inr (Or.inr rfl), fun t h h' => ?_⟩
    change 2 ≤ t ∨ t = 0 at h; change 1 ≤ t ∧ t ≤ 2 at h'
    rcases h with h | h
    · linarith [h'.2]
    · linarith [h'.1]
  · exact absurd rfl hjj

/-- Two distinct sides meet only at a corner. -/
private lemma side_inter_corner {j j' : Fin 3} (hjj : j ≠ j') {z : ℂ} (hz : z ∈ side j)
    (hz' : z ∈ side j') : z = corner 0 ∨ z = corner 1 ∨ z = corner 2 := by
  obtain ⟨t, h0, h3, hs, rfl⟩ := exists_P_of_mem_side hz
  have hs' := (P_mem_side_iff h0 h3).1 hz'
  obtain ⟨c, hc, hc'⟩ := Sd_inter hjj
  have := hc' t hs hs'
  subst this
  rcases hc with rfl | rfl | rfl
  · exact Or.inl P_zero
  · exact Or.inr (Or.inl P_one)
  · exact Or.inr (Or.inr P_two)

/-! ### The vertices -/

/-- The vertices on a chord: its endpoints and its crossings with the other chords. -/
private noncomputable def VC (T : Finset ℝ) (c : ℝ × ℝ) : Finset ℂ :=
  insert (P c.1) (insert (P c.2) (((Ch T).filter (crossR c)).image (X c)))

/-- The vertices on a side: the boundary points on it. -/
private noncomputable def VS (T : Finset ℝ) (j : Fin 3) : Finset ℂ := (T.filter (Sd j)).image P

/-- Membership in `VS T j`. -/
private lemma mem_VS {T : Finset ℝ} {j : Fin 3} {z : ℂ} :
    z ∈ VS T j ↔ ∃ t ∈ T, Sd j t ∧ P t = z := by
  simp only [VS, Finset.mem_image, Finset.mem_filter, and_assoc]

section
variable {T : Finset ℝ} (hT : Good T) {B : Finset ℂ} (hB : B = T.image P)
include hT hB

omit hT in
/-- The points of `B` are the `P t`, `t ∈ T`. -/
private lemma mem_B {z : ℂ} : z ∈ B ↔ ∃ t ∈ T, P t = z := by
  rw [hB, Finset.mem_image]

omit hT in
/-- The points `P t`, `t ∈ T`, are in `B`. -/
private lemma P_mem_B {t : ℝ} (ht : t ∈ T) : P t ∈ B := (mem_B hB).2 ⟨t, ht, rfl⟩

/-- The drawn segments in terms of parameters. -/
private lemma mem_drawn {s : Set ℂ} :
    s ∈ drawn B ↔ ∃ e ∈ T, ∃ f ∈ T, e ≠ f ∧ s = segment ℝ (P e) (P f) := by
  constructor
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    obtain ⟨e, he, rfl⟩ := (mem_B hB).1 hp
    obtain ⟨f, hf, rfl⟩ := (mem_B hB).1 hq
    exact ⟨e, he, f, hf, fun h => hpq (by rw [h]), rfl⟩
  · rintro ⟨e, he, f, hf, hef, rfl⟩
    exact ⟨P e, P_mem_B hB he, P f, P_mem_B hB hf, P_ne_of_ne hT he hf hef, rfl⟩

/-- Chords are drawn. -/
private lemma seg_mem_drawn {c : ℝ × ℝ} (hc : c ∈ Ch T) : seg c ∈ drawn B := by
  rw [mem_Ch] at hc
  exact (mem_drawn hT hB).2 ⟨c.1, hc.1, c.2, hc.2.1, ne_of_lt hc.2.2.1, rfl⟩

omit hB in
/-- A drawn segment is a chord or lies in a side. -/
private lemma classify {e f : ℝ} (he : e ∈ T) (hf : f ∈ T) (hef : e ≠ f) :
    (∃ d ∈ Ch T, segment ℝ (P e) (P f) = seg d) ∨
      (∃ j : Fin 3, Sd j e ∧ Sd j f ∧ segment ℝ (P e) (P f) ⊆ side j) := by
  by_cases hco : coSide e f
  · right
    obtain ⟨j, h1, h2⟩ := (coSide_iff e f).1 hco
    refine ⟨j, h1, h2, (convex_segment _ _).segment_subset ?_ ?_⟩
    · exact P_mem_side (hT e he).1 (hT e he).2 h1
    · exact P_mem_side (hT f hf).1 (hT f hf).2 h2
  · left
    rcases lt_or_gt_of_ne hef with h | h
    · exact ⟨(e, f), mem_Ch.2 ⟨he, hf, h, hco⟩, rfl⟩
    · refine ⟨(f, e), mem_Ch.2 ⟨hf, he, h, fun h' => hco ?_⟩, segment_symm _ _ _⟩
      unfold coSide at h' ⊢; tauto

omit hT hB in
/-- Membership in the vertex set. -/
private lemma mem_vertices {z : ℂ} :
    z ∈ vertices B ↔ z ∈ B ∨ ∃ s ∈ drawn B, ∃ t ∈ drawn B, s ∩ t = {z} := by
  simp only [vertices, Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq]

omit hT hB in
/-- Two drawn segments meeting in a single point are different. -/
private lemma drawn_ne_of_inter {s t : Set ℂ} (hs : s ∈ drawn B) {z : ℂ} (hst : s ∩ t = {z}) :
    s ≠ t := by
  rintro rfl
  rw [Set.inter_self] at hst
  obtain ⟨p, -, q, -, hpq, rfl⟩ := hs
  have h1 : p ∈ segment ℝ p q := left_mem_segment _ _ _
  have h2 : q ∈ segment ℝ p q := right_mem_segment _ _ _
  rw [hst] at h1 h2
  exact hpq (h1.trans h2.symm)

/-- A drawn segment through a point of the relative interior of a chord `c`, other than `c`
itself, is a chord crossing `c` there. -/
private lemma other_seg {c : ℝ × ℝ} (hc : c ∈ Ch T) {z : ℂ} (hz : z ∈ oseg c) {t : Set ℂ}
    (ht : t ∈ drawn B) (hzt : z ∈ t) (htc : t ≠ seg c) :
    ∃ d ∈ Ch T, crossR c d ∧ X c d = z := by
  obtain ⟨g, hg, h, hh, hgh, rfl⟩ := (mem_drawn hT hB).1 ht
  rcases classify hT hg hh hgh with ⟨d, hd, hdt⟩ | ⟨j, -, -, hsub⟩
  · rw [hdt] at hzt htc
    have hcd : c ≠ d := fun e => htc (by rw [e])
    have hcr := crossR_of_mem hT hc hd hcd hz hzt
    refine ⟨d, hd, hcr, ?_⟩
    have : z ∈ seg c ∩ seg d := ⟨openSegment_subset_segment _ _ _ hz, hzt⟩
    rw [seg_inter_X hT hc hd hcr] at this
    exact this.symm
  · exact absurd (hsub hzt) (oseg_not_side hT hc hz j)

/-- The vertices on a chord. -/
private lemma V_chord (hGP : GeneralPosition B) {c : ℝ × ℝ} (hc : c ∈ Ch T) :
    vertices B ∩ seg c = ↑(VC T c) := by
  ext z
  simp only [Set.mem_inter_iff, Finset.mem_coe, VC, Finset.mem_insert, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨hzV, hzc⟩
    by_cases h1 : z = P c.1
    · exact Or.inl h1
    by_cases h2 : z = P c.2
    · exact Or.inr (Or.inl h2)
    right; right
    have hzo : z ∈ oseg c := mem_oseg_of hc hzc h1 h2
    rcases (mem_vertices).1 hzV with hzB | ⟨s, hs, t, ht, hst⟩
    · exfalso
      obtain ⟨u, hu, rfl⟩ := (mem_B hB).1 hzB
      exact P_not_mem_seg hT hc hu (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e])) hzc
    · have hz2 : z ∈ s ∩ t := by rw [hst]; rfl
      have hne := drawn_ne_of_inter hs hst
      rcases hGP z (oseg_interior hT hc hzo) (seg c) (seg_mem_drawn hT hB hc) s hs t ht hzc
        hz2.1 hz2.2 with h | h | h
      · obtain ⟨d, hd, hcr, hX⟩ := other_seg hT hB hc hzo ht hz2.2 (by rw [h]; exact hne.symm)
        exact ⟨d, ⟨hd, hcr⟩, hX⟩
      · obtain ⟨d, hd, hcr, hX⟩ := other_seg hT hB hc hzo hs hz2.1 (by rw [h]; exact hne)
        exact ⟨d, ⟨hd, hcr⟩, hX⟩
      · exact absurd h hne
  · rintro (rfl | rfl | ⟨d, ⟨hd, hcr⟩, rfl⟩)
    · have hc' := (mem_Ch.1 hc).1
      exact ⟨(mem_vertices).2 (Or.inl (P_mem_B hB hc')), left_mem_segment _ _ _⟩
    · have hc' := (mem_Ch.1 hc).2.1
      exact ⟨(mem_vertices).2 (Or.inl (P_mem_B hB hc')), right_mem_segment _ _ _⟩
    · refine ⟨(mem_vertices).2 (Or.inr ⟨seg c, seg_mem_drawn hT hB hc, seg d,
        seg_mem_drawn hT hB hd, seg_inter_X hT hc hd hcr⟩), ?_⟩
      exact openSegment_subset_segment _ _ _ (X_mem hT hc hd hcr).1

omit hT hB in
/-- The corners are in `B`. -/
private lemma corner_mem_B (hcB : ∀ j : Fin 3, corner j ∈ B) {z : ℂ}
    (h : z = corner 0 ∨ z = corner 1 ∨ z = corner 2) : z ∈ B := by
  rcases h with rfl | rfl | rfl <;> exact hcB _

/-- The vertices on a side are the boundary points on it. -/
private lemma V_side (hcB : ∀ j : Fin 3, corner j ∈ B) (j : Fin 3) :
    vertices B ∩ side j = ↑(VS T j) := by
  ext z
  simp only [Set.mem_inter_iff, Finset.mem_coe, mem_VS]
  constructor
  · rintro ⟨hzV, hzj⟩
    have hzB : z ∈ B := by
      rcases (mem_vertices).1 hzV with hzB | ⟨s, hs, t, ht, hst⟩
      · exact hzB
      · by_contra hzB
        have hz2 : z ∈ s ∩ t := by rw [hst]; rfl
        -- each of `s`, `t` lies in a side
        have key : ∀ s ∈ drawn B, z ∈ s → ∃ k : Fin 3, ∃ e ∈ T, ∃ f ∈ T, e ≠ f ∧
            s = segment ℝ (P e) (P f) ∧ Sd k e ∧ Sd k f ∧
            z ∈ openSegment ℝ (P e) (P f) := by
          intro s hs hzs
          obtain ⟨e, he, f, hf, hef, rfl⟩ := (mem_drawn hT hB).1 hs
          have hze : z ≠ P e := fun h => hzB (h ▸ P_mem_B hB he)
          have hzf : z ≠ P f := fun h => hzB (h ▸ P_mem_B hB hf)
          have hzo : z ∈ openSegment ℝ (P e) (P f) := by
            rw [← insert_endpoints_openSegment] at hzs
            rcases hzs with h | h | h
            · exact absurd h hze
            · exact absurd h hzf
            · exact h
          rcases classify hT he hf hef with ⟨d, hd, hdt⟩ | ⟨k, h1, h2, -⟩
          · exfalso
            rw [hdt] at hzs
            have hd' := mem_Ch.1 hd
            have := mem_oseg_of hd hzs (fun h => hzB (h ▸ P_mem_B hB hd'.1))
              (fun h => hzB (h ▸ P_mem_B hB hd'.2.1))
            exact oseg_not_side hT hd this j hzj
          · exact ⟨k, e, he, f, hf, hef, rfl, h1, h2, hzo⟩
        obtain ⟨k, e, he, f, hf, hef, rfl, he1, hf1, hzo1⟩ := key s hs hz2.1
        obtain ⟨k', g, hg, h, hh, hgh, rfl, hg1, hh1, hzo2⟩ := key t ht hz2.2
        have hzk : z ∈ side k := (convex_segment _ _).segment_subset
          (P_mem_side (hT e he).1 (hT e he).2 he1) (P_mem_side (hT f hf).1 (hT f hf).2 hf1)
          (openSegment_subset_segment _ _ _ hzo1)
        have hzk' : z ∈ side k' := (convex_segment _ _).segment_subset
          (P_mem_side (hT g hg).1 (hT g hg).2 hg1) (P_mem_side (hT h hh).1 (hT h hh).2 hh1)
          (openSegment_subset_segment _ _ _ hzo2)
        by_cases hkk : k = k'
        · subst hkk
          obtain ⟨w, hwz, hw1, hw2⟩ := oneD (corner_ne k)
            (P_mem_side (hT e he).1 (hT e he).2 he1) (P_mem_side (hT f hf).1 (hT f hf).2 hf1)
            (P_mem_side (hT g hg).1 (hT g hg).2 hg1) (P_mem_side (hT h hh).1 (hT h hh).2 hh1)
            (P_ne_of_ne hT he hf hef) (P_ne_of_ne hT hg hh hgh) hzo1 hzo2
          have : w ∈ segment ℝ (P e) (P f) ∩ segment ℝ (P g) (P h) := ⟨hw1, hw2⟩
          rw [hst] at this
          exact hwz this
        · exact hzB (corner_mem_B hcB (side_inter_corner hkk hzk hzk'))
    obtain ⟨u, hu, rfl⟩ := (mem_B hB).1 hzB
    exact ⟨u, hu, (P_mem_side_iff (hT u hu).1 (hT u hu).2).1 hzj, rfl⟩
  · rintro ⟨u, hu, hsd, rfl⟩
    exact ⟨(mem_vertices).2 (Or.inl (P_mem_B hB hu)),
      P_mem_side (hT u hu).1 (hT u hu).2 hsd⟩

end

/-! ### Consecutive points on a segment -/

open Classical in
/-- Consecutive pairs of a finite set of reals. -/
private noncomputable def consR (T : Finset ℝ) : Finset (ℝ × ℝ) :=
  (T ×ˢ T).filter (fun p => p.1 < p.2 ∧ ∀ w ∈ T, ¬ (p.1 < w ∧ w < p.2))

/-- Membership in `consR T`. -/
private lemma mem_consR {T : Finset ℝ} {p : ℝ × ℝ} :
    p ∈ consR T ↔ p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 < p.2 ∧ ∀ w ∈ T, ¬ (p.1 < w ∧ w < p.2) := by
  simp only [consR, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- A nonempty finite set of reals has one consecutive pair fewer than elements. -/
private lemma consR_card (T : Finset ℝ) (hT : T.Nonempty) : (consR T).card + 1 = T.card := by
  classical
  induction T using Finset.induction_on_max with
  | empty => exact absurd hT (by simp)
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rcases s.eq_empty_or_nonempty with rfl | hs
    · have : consR {a} = ∅ := by
        ext ⟨u, v⟩
        simp only [mem_consR, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨rfl, rfl, h, -⟩
        exact lt_irrefl _ h
      simp [this]
    · have e : consR (insert a s) = insert (s.max' hs, a) (consR s) := by
        ext ⟨u, v⟩
        simp only [mem_consR, Finset.mem_insert, Prod.mk.injEq]
        constructor
        · rintro ⟨hu, hv, huv, hw⟩
          rcases hv with rfl | hv
          · left
            have hu' : u ∈ s := hu.resolve_left (ne_of_lt huv)
            refine ⟨?_, rfl⟩
            have hle := s.le_max' u hu'
            rcases lt_or_eq_of_le hle with hlt' | heq
            · exact absurd ⟨hlt', hlt _ (s.max'_mem hs)⟩ (hw _ (Or.inr (s.max'_mem hs)))
            · exact heq
          · right
            have hva := hlt v hv
            have hu' : u ∈ s := hu.resolve_left (by intro h; subst h; linarith)
            exact ⟨hu', hv, huv, fun w hws => hw w (Or.inr hws)⟩
        · rintro (⟨rfl, rfl⟩ | ⟨hu, hv, huv, hw⟩)
          · refine ⟨Or.inr (s.max'_mem hs), Or.inl rfl, hlt _ (s.max'_mem hs), ?_⟩
            rintro w (rfl | hws) ⟨h1, h2⟩
            · exact lt_irrefl _ h2
            · exact absurd (s.le_max' w hws) (not_le.2 h1)
          · refine ⟨Or.inr hu, Or.inr hv, huv, ?_⟩
            rintro w (rfl | hws)
            · rintro ⟨-, h2⟩; exact lt_irrefl _ (lt_trans h2 (hlt v hv))
            · exact hw w hws
      have hnot : (s.max' hs, a) ∉ consR s := by
        rw [mem_consR]; exact fun h => has h.2.1
      rw [e, Finset.card_insert_of_notMem hnot, Finset.card_insert_of_notMem has, ← ih hs]

open Classical in
/-- The pairs of points of `F` with no point of `F` strictly between them. -/
private noncomputable def consF (F : Finset ℂ) : Finset (Sym2 ℂ) :=
  ((F ×ˢ F).filter (fun p => p.1 ≠ p.2 ∧ ∀ w ∈ F, w ∉ openSegment ℝ p.1 p.2)).image
    (fun p => s(p.1, p.2))

/-- Membership in `consF F`. -/
private lemma mem_consF {F : Finset ℂ} {e : Sym2 ℂ} :
    e ∈ consF F ↔ ∃ u v, u ∈ F ∧ v ∈ F ∧ u ≠ v ∧ (∀ w ∈ F, w ∉ openSegment ℝ u v) ∧
      e = s(u, v) := by
  simp only [consF, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨u, v, ⟨⟨hu, hv⟩, huv, hw⟩, rfl⟩; exact ⟨u, v, hu, hv, huv, hw, rfl⟩
  · rintro ⟨u, v, hu, hv, huv, hw, rfl⟩; exact ⟨u, v, ⟨⟨hu, hv⟩, huv, hw⟩, rfl⟩

/-- Membership of a pair in `consF F`. -/
private lemma mem_consF_pair {F : Finset ℂ} {u v : ℂ} :
    s(u, v) ∈ consF F ↔ u ≠ v ∧ u ∈ F ∧ v ∈ F ∧ ∀ w ∈ F, w ∉ openSegment ℝ u v := by
  rw [mem_consF]
  constructor
  · rintro ⟨u', v', hu, hv, huv, hw, he⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨huv, hu, hv, hw⟩
    · refine ⟨huv.symm, hv, hu, ?_⟩
      intro w hwF; rw [openSegment_symm]; exact hw w hwF
  · rintro ⟨huv, hu, hv, hw⟩
    exact ⟨u, v, hu, hv, huv, hw, rfl⟩

/-- A nonempty finite subset of a segment has one consecutive pair fewer than elements. -/
private lemma consF_card {a b : ℂ} (hab : a ≠ b) (F : Finset ℂ) (hF : ↑F ⊆ segment ℝ a b)
    (hne : F.Nonempty) : (consF F).card + 1 = F.card := by
  classical
  set f : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  set T := F.preimage f hf.injOn
  have hFT : F = T.image f := by
    ext z
    simp only [Finset.mem_image, T, Finset.mem_preimage]
    constructor
    · intro hz
      have := hF hz
      rw [segment_eq_image_lineMap] at this
      obtain ⟨t, -, rfl⟩ := this
      exact ⟨t, hz, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ht
  have hseg : ∀ α β : ℝ, α < β → ∀ γ : ℝ, f γ ∈ openSegment ℝ (f α) (f β) ↔ α < γ ∧ γ < β := by
    intro α β hαβ γ
    rw [← image_openSegment, openSegment_eq_Ioo hαβ]
    constructor
    · rintro ⟨γ', hγ', h⟩; rw [← hf h]; exact hγ'
    · intro h; exact ⟨γ, h, rfl⟩
  have e : consF F = (consR T).image (fun p => s(f p.1, f p.2)) := by
    ext e
    rw [mem_consF, Finset.mem_image]
    constructor
    · rintro ⟨u, v, hu, hv, huv, hw, rfl⟩
      rw [hFT, Finset.mem_image] at hu hv
      obtain ⟨α, hα, rfl⟩ := hu
      obtain ⟨β, hβ, rfl⟩ := hv
      have hne' : α ≠ β := fun h => huv (by rw [h])
      rcases lt_or_gt_of_ne hne' with hlt | hlt
      · refine ⟨(α, β), mem_consR.2 ⟨hα, hβ, hlt, fun γ hγ hb => ?_⟩, rfl⟩
        exact hw (f γ) (by rw [hFT]; exact Finset.mem_image_of_mem _ hγ) ((hseg α β hlt γ).2 hb)
      · refine ⟨(β, α), mem_consR.2 ⟨hβ, hα, hlt, fun γ hγ hb => ?_⟩, Sym2.eq_swap⟩
        rw [openSegment_symm] at hw
        exact hw (f γ) (by rw [hFT]; exact Finset.mem_image_of_mem _ hγ) ((hseg β α hlt γ).2 hb)
    · rintro ⟨⟨α, β⟩, hp, rfl⟩
      rw [mem_consR] at hp
      obtain ⟨hα, hβ, hlt, hw⟩ := hp
      refine ⟨f α, f β, ?_, ?_, fun h => ne_of_lt hlt (hf h), ?_, rfl⟩
      · rw [hFT]; exact Finset.mem_image_of_mem _ hα
      · rw [hFT]; exact Finset.mem_image_of_mem _ hβ
      · intro w hwF hwseg
        rw [hFT, Finset.mem_image] at hwF
        obtain ⟨γ, hγ, rfl⟩ := hwF
        exact hw γ hγ ((hseg α β hlt γ).1 hwseg)
  have hinj : Set.InjOn (fun p : ℝ × ℝ => s(f p.1, f p.2)) ↑(consR T) := by
    rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq h
    simp only [Finset.mem_coe, mem_consR] at hp hq
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hf h1, hf h2]
    · have := hf h1; have := hf h2
      exfalso; linarith [hp.2.2.1, hq.2.2.1]
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    rw [hFT, Finset.mem_image] at hz
    obtain ⟨t, ht, -⟩ := hz
    exact ⟨t, ht⟩
  rw [e, Finset.card_image_of_injOn hinj, consR_card T hTne, hFT,
    Finset.card_image_of_injective _ hf]

/-- Sets with no two common points have disjoint `consF`. -/
private lemma disjoint_consF {F G : Finset ℂ}
    (h : ∀ u v, u ≠ v → u ∈ F → v ∈ F → u ∈ G → v ∈ G → False) :
    Disjoint (consF F) (consF G) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨u, v, hu, hv, huv, -, rfl⟩ := mem_consF.1 h1
  obtain ⟨-, hu', hv', -⟩ := mem_consF_pair.1 h2
  exact h u v huv hu hv hu' hv'

/-! ### The planar graph -/

/-- Adjacency in the planar graph. -/
private lemma adj_iff {B : Finset ℂ} {u v : ℂ} : (planarGraph B).Adj u v ↔
    u ≠ v ∧ u ∈ vertices B ∧ v ∈ vertices B ∧ (∃ s ∈ drawn B, u ∈ s ∧ v ∈ s) ∧
      ∀ w ∈ vertices B, w ∉ openSegment ℝ u v := by
  rw [planarGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨huv, h | h⟩
    · exact ⟨huv, h⟩
    · obtain ⟨hv, hu, ⟨s, hs, hvs, hus⟩, hw⟩ := h
      refine ⟨huv, hu, hv, ⟨s, hs, hus, hvs⟩, fun w hwV => ?_⟩
      rw [openSegment_symm]; exact hw w hwV
  · rintro ⟨huv, h⟩; exact ⟨huv, Or.inl h⟩

/-- Edges inside a convex piece `M` of the drawing whose vertices are `F`. -/
private lemma consF_iff {B : Finset ℂ} {M : Set ℂ} (hM : Convex ℝ M) {F : Finset ℂ}
    (hF : vertices B ∩ M = ↑F) {u v : ℂ} :
    s(u, v) ∈ consF F ↔ u ≠ v ∧ u ∈ vertices B ∧ v ∈ vertices B ∧ u ∈ M ∧ v ∈ M ∧
      ∀ w ∈ vertices B, w ∉ openSegment ℝ u v := by
  have key : ∀ z, z ∈ F ↔ z ∈ vertices B ∧ z ∈ M := by
    intro z; rw [← Finset.mem_coe, ← hF]; rfl
  rw [mem_consF_pair, key u, key v]
  constructor
  · rintro ⟨huv, ⟨hu, huM⟩, ⟨hv, hvM⟩, hw⟩
    refine ⟨huv, hu, hv, huM, hvM, fun w hwV hwo => ?_⟩
    exact hw w ((key w).2 ⟨hwV, hM.segment_subset huM hvM
      (openSegment_subset_segment _ _ _ hwo)⟩) hwo
  · rintro ⟨huv, hu, hv, huM, hvM, hw⟩
    exact ⟨huv, ⟨hu, huM⟩, ⟨hv, hvM⟩, fun w hwF => hw w ((key w).1 hwF).1⟩

/-- A chord does not cross itself. -/
private lemma crossR_irrefl (c : ℝ × ℝ) : ¬ crossR c c := by
  unfold crossR
  rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> exact lt_irrefl _ h1

/-- The edge set as a finite set. -/
private noncomputable def EF (T : Finset ℝ) : Finset (Sym2 ℂ) :=
  (Finset.univ.biUnion fun j => consF (VS T j)) ∪ ((Ch T).biUnion fun c => consF (VC T c))

section
variable {T : Finset ℝ} (hT : Good T) {B : Finset ℂ} (hB : B = T.image P)
  (hGP : GeneralPosition B) (hcB : ∀ j : Fin 3, corner j ∈ B)
include hT hB hGP hcB

omit hT hB hGP in
/-- The sides are drawn. -/
private lemma side_mem_drawn (j : Fin 3) : side j ∈ drawn B :=
  ⟨corner j, hcB j, corner (j + 1), hcB (j + 1), corner_ne j, rfl⟩

/-- The edge set is the union of the consecutive pairs on the sides and on the chords. -/
private lemma edgeSet_eq : (planarGraph B).edgeSet = ↑(EF T) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
  rw [SimpleGraph.mem_edgeSet, adj_iff, Finset.mem_coe, EF, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨huv, hu, hv, ⟨s, hs, hus, hvs⟩, hw⟩
    obtain ⟨e, he, f, hf, hef, rfl⟩ := (mem_drawn hT hB).1 hs
    rcases classify hT he hf hef with ⟨d, hd, hdt⟩ | ⟨j, -, -, hsub⟩
    · right
      rw [hdt] at hus hvs
      exact ⟨d, hd, (consF_iff (convex_segment _ _) (V_chord hT hB hGP hd)).2
        ⟨huv, hu, hv, hus, hvs, hw⟩⟩
    · left
      exact ⟨j, Finset.mem_univ _, (consF_iff (convex_segment _ _) (V_side hT hB hcB j)).2
        ⟨huv, hu, hv, hsub hus, hsub hvs, hw⟩⟩
  · rintro (⟨j, -, h⟩ | ⟨c, hc, h⟩)
    · obtain ⟨huv, hu, hv, huM, hvM, hw⟩ :=
        (consF_iff (convex_segment _ _) (V_side hT hB hcB j)).1 h
      exact ⟨huv, hu, hv, ⟨side j, side_mem_drawn hcB j, huM, hvM⟩, hw⟩
    · obtain ⟨huv, hu, hv, huM, hvM, hw⟩ :=
        (consF_iff (convex_segment _ _) (V_chord hT hB hGP hc)).1 h
      exact ⟨huv, hu, hv, ⟨seg c, seg_mem_drawn hT hB hc, huM, hvM⟩, hw⟩

omit hGP in
/-- The vertices of a side lie on it. -/
private lemma VS_sub (j : Fin 3) : ↑(VS T j) ⊆ side j := by
  rw [← V_side hT hB hcB j]; exact Set.inter_subset_right

omit hcB in
/-- The vertices of a chord lie on it. -/
private lemma VC_sub {c : ℝ × ℝ} (hc : c ∈ Ch T) : ↑(VC T c) ⊆ seg c := by
  rw [← V_chord hT hB hGP hc]; exact Set.inter_subset_right

omit hB hGP hcB in
/-- Distinct chords are distinct segments. -/
private lemma seg_ne {c d : ℝ × ℝ} (hc : c ∈ Ch T) (hd : d ∈ Ch T) (hcd : c ≠ d) :
    seg c ≠ seg d := by
  intro h
  have h1 : P c.1 ∈ seg c := left_mem_segment _ _ _
  have h2 : P c.2 ∈ seg c := right_mem_segment _ _ _
  have h1' := h1; have h2' := h2
  rw [h] at h1' h2'
  exact chord_ne hT hc (seg_inter_unique hT hc hd hcd h1 h1' h2 h2')

omit hcB in
/-- A chord carries its two endpoints and one vertex for each chord crossing it. -/
private lemma VC_card {c : ℝ × ℝ} (hc : c ∈ Ch T) :
    (VC T c).card = ((Ch T).filter (crossR c)).card + 2 := by
  have hX : ∀ d ∈ (Ch T).filter (crossR c), X c d ∈ oseg c := by
    intro d hd
    rw [Finset.mem_filter] at hd
    exact (X_mem hT hc hd.1 hd.2).1
  have hne := endpoint_not_oseg hT hc
  have hinj : Set.InjOn (X c) ↑((Ch T).filter (crossR c)) := by
    intro d hd d' hd' hdd
    by_contra hne'
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hd hd'
    have hz := X_mem hT hc hd.1 hd.2
    have hz' := X_mem hT hc hd'.1 hd'.2
    rw [← hdd] at hz'
    have hcd : c ≠ d := fun e => crossR_irrefl c (e ▸ hd.2)
    have hcd' : c ≠ d' := fun e => crossR_irrefl c (e ▸ hd'.2)
    rcases hGP (X c d) (oseg_interior hT hc hz.1) (seg c) (seg_mem_drawn hT hB hc)
      (seg d) (seg_mem_drawn hT hB hd.1) (seg d') (seg_mem_drawn hT hB hd'.1)
      (openSegment_subset_segment _ _ _ hz.1) (openSegment_subset_segment _ _ _ hz.2)
      (openSegment_subset_segment _ _ _ hz'.2) with h | h | h
    · exact seg_ne hT hc hd.1 hcd h
    · exact seg_ne hT hc hd'.1 hcd' h
    · exact seg_ne hT hd.1 hd'.1 hne' h
  rw [VC, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_image_of_injOn hinj]
  · intro h
    obtain ⟨d, hd, e⟩ := Finset.mem_image.1 h
    exact hne.2 (e ▸ hX d hd)
  · intro h
    rw [Finset.mem_insert] at h
    rcases h with h | h
    · exact chord_ne hT hc h
    · obtain ⟨d, hd, e⟩ := Finset.mem_image.1 h
      exact hne.1 (e ▸ hX d hd)

omit hB hGP hcB in
/-- A side carries one vertex per parameter of the side. -/
private lemma VS_card (j : Fin 3) : (VS T j).card = (T.filter (Sd j)).card := by
  classical
  rw [VS, Finset.card_image_of_injOn]
  intro s hs t ht h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs ht
  exact P_injT hT hs.1 ht.1 h

/-- The edge count is the sum over the sides and the chords. -/
private lemma EF_card :
    (EF T).card = ∑ j, (consF (VS T j)).card + ∑ c ∈ Ch T, (consF (VC T c)).card := by
  have hC : ((Ch T : Set (ℝ × ℝ))).PairwiseDisjoint (fun c => consF (VC T c)) := by
    intro c hc d hd hcd
    apply disjoint_consF
    intro u v huv hu hv hu' hv'
    exact huv (seg_inter_unique hT hc hd hcd (VC_sub hT hB hGP hc hu)
      (VC_sub hT hB hGP hd hu') (VC_sub hT hB hGP hc hv) (VC_sub hT hB hGP hd hv'))
  have hS : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      (fun j => consF (VS T j)) := by
    intro j _ j' _ hjj
    apply disjoint_consF
    intro u v huv hu hv hu' hv'
    obtain ⟨c, -, hc⟩ := Sd_inter hjj
    obtain ⟨s, hs, hs1, rfl⟩ := mem_VS.1 hu
    obtain ⟨t, ht, ht1, rfl⟩ := mem_VS.1 hv
    obtain ⟨s', hs', hs2, e1⟩ := mem_VS.1 hu'
    obtain ⟨t', ht', ht2, e2⟩ := mem_VS.1 hv'
    rw [P_injT hT hs' hs e1] at hs2
    rw [P_injT hT ht' ht e2] at ht2
    exact huv (by rw [hc s hs1 hs2, hc t ht1 ht2])
  have hD : Disjoint (Finset.univ.biUnion fun j => consF (VS T j))
      ((Ch T).biUnion fun c => consF (VC T c)) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rw [Finset.mem_biUnion] at h1 h2
    obtain ⟨j, -, hj⟩ := h1
    obtain ⟨c, hc, hcc⟩ := h2
    obtain ⟨u, v, hu, hv, huv, -, rfl⟩ := mem_consF.1 hj
    obtain ⟨-, hu', hv', -⟩ := mem_consF_pair.1 hcc
    have hus := VS_sub hT hB hcB j hu
    have hvs := VS_sub hT hB hcB j hv
    have huc := VC_sub hT hB hGP hc hu'
    have hvc := VC_sub hT hB hGP hc hv'
    have hend : ∀ z, z ∈ side j → z ∈ seg c → z = P c.1 ∨ z = P c.2 := by
      intro z hz hz'
      by_contra hn
      push Not at hn
      exact oseg_not_side hT hc (mem_oseg_of hc hz' hn.1 hn.2) j hz
    have hc' := mem_Ch.1 hc
    have key : P c.1 ∈ side j ∧ P c.2 ∈ side j := by
      rcases hend u hus huc with h1 | h1 <;> rcases hend v hvs hvc with h2 | h2
      · exact absurd (h1.trans h2.symm) huv
      · exact ⟨h1 ▸ hus, h2 ▸ hvs⟩
      · exact ⟨h2 ▸ hvs, h1 ▸ hus⟩
      · exact absurd (h1.trans h2.symm) huv
    have k1 := (P_mem_side_iff (hT _ hc'.1).1 (hT _ hc'.1).2).1 key.1
    have k2 := (P_mem_side_iff (hT _ hc'.2.1).1 (hT _ hc'.2.1).2).1 key.2
    exact hc'.2.2.2 ((coSide_iff _ _).2 ⟨j, k1, k2⟩)
  rw [EF, Finset.card_union_of_disjoint hD, Finset.card_biUnion hS, Finset.card_biUnion hC]

/-- The number of edges, from the parameters. -/
private lemma edges_eq : edges B =
    ∑ j, ((T.filter (Sd j)).card - 1) + ∑ c ∈ Ch T, (((Ch T).filter (crossR c)).card + 1) := by
  rw [edges, edgeSet_eq hT hB hGP hcB, Set.ncard_coe_finset, EF_card hT hB hGP hcB]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hne : (VS T j).Nonempty := ⟨corner j, by
      rw [← Finset.mem_coe, ← V_side hT hB hcB j]
      exact ⟨(mem_vertices).2 (Or.inl (hcB j)), left_mem_segment _ _ _⟩⟩
    have := consF_card (corner_ne j) (VS T j) (VS_sub hT hB hcB j) hne
    rw [VS_card hT j] at this
    omega
  · refine Finset.sum_congr rfl fun c hc => ?_
    have hne : (VC T c).Nonempty := ⟨P c.1, Finset.mem_insert_self _ _⟩
    have := consF_card (chord_ne hT hc) (VC T c) (VC_sub hT hB hGP hc) hne
    rw [VC_card hT hB hGP hc] at this
    omega

end

/-- The open parameter interval of side 0. -/
private lemma Od_zero (t : ℝ) : Od 0 t ↔ 0 < t ∧ t < 1 := Iff.rfl
/-- The open parameter interval of side 1. -/
private lemma Od_one (t : ℝ) : Od 1 t ↔ 1 < t ∧ t < 2 := Iff.rfl
/-- The open parameter interval of side 2. -/
private lemma Od_two (t : ℝ) : Od 2 t ↔ 2 < t := Iff.rfl

/-- The parameters of a placement. -/
private lemma exists_T {n : ℕ} {B : Finset ℂ} (hB : IsPlacement n B) :
    ∃ T : Finset ℝ, Good T ∧ B = T.image P ∧ T.card = 3 * n + 3 ∧
      (T.filter S0).card = n + 2 ∧ (T.filter S1).card = n + 2 ∧ (T.filter S2).card = n + 2 := by
  obtain ⟨hc, hs, ho⟩ := hB
  have key : ∀ z ∈ B, 0 ≤ θ z ∧ θ z < 3 ∧ P (θ z) = z := by
    intro z hz
    obtain ⟨j, hj⟩ := hs z hz
    obtain ⟨t, h0, h3, -, rfl⟩ := exists_P_of_mem_side (j := j) hj
    rw [θ_P h0 h3]; exact ⟨h0, h3, rfl⟩
  set T := B.image θ with hTdef
  have hT : Good T := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ht
    exact ⟨(key z hz).1, (key z hz).2.1⟩
  have hBT : B = T.image P := by
    ext z
    rw [Finset.mem_image]
    constructor
    · intro hz; exact ⟨θ z, Finset.mem_image_of_mem _ hz, (key z hz).2.2⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 ht
      rw [(key w hw).2.2]; exact hw
  have hPB : ∀ t ∈ T, P t ∈ B := by
    intro t ht; rw [hBT]; exact Finset.mem_image_of_mem _ ht
  have hmemT : ∀ t : ℝ, 0 ≤ t → t < 3 → P t ∈ B → t ∈ T := by
    intro t h0 h3 hP
    rw [← θ_P h0 h3]; exact Finset.mem_image_of_mem _ hP
  have h0T : (0:ℝ) ∈ T := hmemT 0 (le_refl _) (by norm_num) (P_zero ▸ hc 0)
  have h1T : (1:ℝ) ∈ T := hmemT 1 (by norm_num) (by norm_num) (P_one ▸ hc 1)
  have h2T : (2:ℝ) ∈ T := hmemT 2 (by norm_num) (by norm_num) (P_two ▸ hc 2)
  have hO : ∀ j : Fin 3, (T.filter (Od j)).card = n := by
    intro j
    have e : (B : Set ℂ) ∩ openSegment ℝ (corner j) (corner (j + 1)) =
        ↑((T.filter (Od j)).image P) := by
      ext z
      simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.coe_image, Finset.coe_filter,
        Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hz, hzo⟩
        have hk := key z hz
        refine ⟨θ z, ⟨Finset.mem_image_of_mem _ hz, ?_⟩, hk.2.2⟩
        rw [← P_mem_openSide_iff hk.1 hk.2.1, hk.2.2]; exact hzo
      · rintro ⟨t, ⟨ht, hod⟩, rfl⟩
        exact ⟨hPB t ht, (P_mem_openSide_iff (hT t ht).1 (hT t ht).2).2 hod⟩
    have := ho j
    rw [e, Set.ncard_coe_finset, Finset.card_image_of_injOn] at this
    · exact this
    · intro s hs t ht h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs ht
      exact P_injT hT hs.1 ht.1 h
  have hO0 := hO 0
  have hO1 := hO 1
  have hO2 := hO 2
  refine ⟨T, hT, hBT, ?_, ?_, ?_, ?_⟩
  · have e : T = insert 0 (insert 1 (insert 2
        ((T.filter (Od 0) ∪ T.filter (Od 1)) ∪ T.filter (Od 2)))) := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Od_zero, Od_one,
        Od_two]
      constructor
      · intro ht
        obtain ⟨h0, h3⟩ := hT t ht
        rcases eq_or_lt_of_le h0 with h | h
        · exact Or.inl h.symm
        rcases lt_trichotomy t 1 with h1 | h1 | h1
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨ht, h, h1⟩))))
        · exact Or.inr (Or.inl h1)
        rcases lt_trichotomy t 2 with h2 | h2 | h2
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨ht, h1, h2⟩))))
        · exact Or.inr (Or.inr (Or.inl h2))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, h2⟩)))
      · rintro (rfl | rfl | rfl | ((⟨ht, -⟩ | ⟨ht, -⟩) | ⟨ht, -⟩))
        · exact h0T
        · exact h1T
        · exact h2T
        · exact ht
        · exact ht
        · exact ht
    have d1 : Disjoint (T.filter (Od 0)) (T.filter (Od 1)) := by
      rw [Finset.disjoint_left]
      intro t h h'
      simp only [Finset.mem_filter, Od_zero, Od_one] at h h'
      linarith [h.2.2, h'.2.1]
    have d2 : Disjoint (T.filter (Od 0) ∪ T.filter (Od 1)) (T.filter (Od 2)) := by
      rw [Finset.disjoint_left]
      intro t h h'
      simp only [Finset.mem_union, Finset.mem_filter, Od_zero, Od_one, Od_two] at h h'
      rcases h with h | h
      · linarith [h.2.2]
      · linarith [h.2.2]
    rw [e, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_union_of_disjoint d2,
      Finset.card_union_of_disjoint d1, hO0, hO1, hO2]
    · ring
    · simp only [Finset.mem_union, Finset.mem_filter, Od_zero, Od_one, Od_two]
      norm_num
    · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Od_zero, Od_one,
        Od_two]
      norm_num
    · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Od_zero, Od_one,
        Od_two]
      norm_num
  · have e : T.filter S0 = insert 0 (insert 1 (T.filter (Od 0))) := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_filter, Od_zero, S0]
      constructor
      · rintro ⟨ht, h1⟩
        obtain ⟨h0, -⟩ := hT t ht
        rcases eq_or_lt_of_le h0 with h | h
        · exact Or.inl h.symm
        rcases eq_or_lt_of_le h1 with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr ⟨ht, h, h'⟩)
      · rintro (rfl | rfl | ⟨ht, -, h⟩)
        · exact ⟨h0T, by norm_num⟩
        · exact ⟨h1T, le_refl _⟩
        · exact ⟨ht, h.le⟩
    rw [e, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, hO0]
    · simp only [Finset.mem_filter, Od_zero]; norm_num
    · simp only [Finset.mem_insert, Finset.mem_filter, Od_zero]; norm_num
  · have e : T.filter S1 = insert 1 (insert 2 (T.filter (Od 1))) := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_filter, Od_one, S1]
      constructor
      · rintro ⟨ht, h1, h2⟩
        rcases eq_or_lt_of_le h1 with h | h
        · exact Or.inl h.symm
        rcases eq_or_lt_of_le h2 with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr ⟨ht, h, h'⟩)
      · rintro (rfl | rfl | ⟨ht, h, h'⟩)
        · exact ⟨h1T, le_refl _, by norm_num⟩
        · exact ⟨h2T, by norm_num, le_refl _⟩
        · exact ⟨ht, h.le, h'.le⟩
    rw [e, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, hO1]
    · simp only [Finset.mem_filter, Od_one]; norm_num
    · simp only [Finset.mem_insert, Finset.mem_filter, Od_one]; norm_num
  · have e : T.filter S2 = insert 2 (insert 0 (T.filter (Od 2))) := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_filter, Od_two, S2]
      constructor
      · rintro ⟨ht, h | h⟩
        · rcases eq_or_lt_of_le h with h' | h'
          · exact Or.inl h'.symm
          · exact Or.inr (Or.inr ⟨ht, h'⟩)
        · exact Or.inr (Or.inl h)
      · rintro (rfl | rfl | ⟨ht, h⟩)
        · exact ⟨h2T, Or.inl (le_refl _)⟩
        · exact ⟨h0T, Or.inr rfl⟩
        · exact ⟨ht, Or.inl h.le⟩
    rw [e, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, hO2]
    · simp only [Finset.mem_filter, Od_two]; norm_num
    · simp only [Finset.mem_insert, Finset.mem_filter, Od_two]; norm_num

/-- The conjecture of A367119: the all-chords graph of a triangle with `n` points in general
position on each side has `(3/2)(3n^4 + 4n^3 + 3n^2 + 4n + 2)` edges. -/
theorem result : statement := by
  intro n B hB hGP
  have hcB : ∀ j : Fin 3, corner j ∈ B := hB.1
  obtain ⟨T, hT, hBT, hN, c0, c1, c2⟩ := exists_T hB
  have e0 : T.filter (Sd 0) = T.filter S0 := Finset.filter_congr (fun x _ => Iff.rfl)
  have e1 : T.filter (Sd 1) = T.filter S1 := Finset.filter_congr (fun x _ => Iff.rfl)
  have e2 : T.filter (Sd 2) = T.filter S2 := Finset.filter_congr (fun x _ => Iff.rfl)
  have hE : edges B = 3 * (n + 1) +
      ((∑ c ∈ Ch T, ((Ch T).filter (crossR c)).card) + (Ch T).card) := by
    rw [edges_eq hT hBT hGP hcB, Fin.sum_univ_three, e0, e1, e2, c0, c1, c2,
      Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    omega
  have h1 := crossings_formula n T (fun t ht => (hT t ht).1) hN c0 c1 c2
  have h2 := chords_card n T hN c0 c1 c2
  rw [hE, Nat.cast_add, Nat.cast_add, h1, h2]
  push_cast
  ring

end Math0.Frontier.A367119

#math0_settles Math0.Frontier.A367119.result Math0.Statements.A367119.statement
