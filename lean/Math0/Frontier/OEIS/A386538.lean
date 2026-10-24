/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A386538
import Math0.Audit

/-!
# A386538: a non-lattice center gives a larger lattice polygon (counterexample at `n = 7`)

The conjecture says that the largest area of a polygon with vertices on the unit grid inside a
circle of radius `n` does not grow when the center of the circle is allowed to be any point of
the plane instead of a grid point. We refute it at `n = 7` with the center `c0 = (5/12, 5/24)`.

* Upper bound (lattice center). Every grid point `(x, y)` with `x² + y² ≤ 49` satisfies the twelve
  inequalities `±3x ± y ≤ 21`, `±x ± y ≤ 9`, `±x ± 3y ≤ 21` (a kernel-checked finite check).
  Their solution set is convex (the 12-gon with vertices `(±7, 0), (±6, ±3), (±3, ±6), (0, ±7)`),
  so it contains the convex hull. Cutting this 12-gon by the vertical lines `x = -6, -3, 0, 3, 6`
  gives six trapezoids; thickening each vertically by `1/100` makes it a `regionBetween` of two
  affine functions over a closed interval, whose volume is an explicit integral. Hence the hull
  has area at most `138 + 28/100 = 3457/25` (its true area is `138`).
* Lower bound (center `c0`). For each `x ∈ {-6, …, 7}` let `lo x` and `hi x` be the lowest and
  highest grid points in the disk of radius `7` around `c0` on the vertical line through `x`.
  Joining consecutive columns gives eleven trapezoids (open in both directions, pairwise disjoint)
  whose corners are grid points in that disk. Each trapezoid lies in the convex hull because its
  points are convex combinations of its corners, and the trapezoids have total area `277/2`.
* Since `3457/25 < 277/2`, the hull for the center `c0` is strictly larger than the hull for the
  lattice center, so `⨆ c, maxArea c 7 > maxArea 0 7`.
-/

namespace Math0.Frontier.A386538

open Math0.Statements.A386538 MeasureTheory Set

/-- A trapezoid over the closed interval `[a, b]`, between the lines `y = p x + q` and
`y = r x + t` (open in the vertical direction). -/
private def upSlab (a b p q r t : ℝ) : Set (ℝ × ℝ) :=
  regionBetween (fun x => p * x + q) (fun x => r * x + t) (Icc a b)

/-- A trapezoid over the open interval `(a, b)`, strictly between the lines `y = p x + q` and
`y = r x + t`. -/
private def lowSlab (a b p q r t : ℝ) : Set (ℝ × ℝ) :=
  regionBetween (fun x => p * x + q) (fun x => r * x + t) (Ioo a b)

/-- Membership in `upSlab`. -/
private lemma mem_upSlab {a b p q r t : ℝ} {z : ℝ × ℝ} (h1 : a ≤ z.1) (h2 : z.1 ≤ b)
    (h3 : p * z.1 + q < z.2) (h4 : z.2 < r * z.1 + t) : z ∈ upSlab a b p q r t :=
  ⟨⟨h1, h2⟩, h3, h4⟩

/-- Points of `lowSlab a b …` have first coordinate in `(a, b)`. -/
private lemma lowSlab_fst {a b p q r t : ℝ} {z : ℝ × ℝ} (h : z ∈ lowSlab a b p q r t) :
    a < z.1 ∧ z.1 < b := h.1

/-- `lowSlab a b …` lies to the right of every `c ≤ a`. -/
private lemma lowSlab_subset_ge {a b p q r t c : ℝ} (hc : c ≤ a) :
    lowSlab a b p q r t ⊆ {z | c ≤ z.1} := fun _ hz => hc.trans (lowSlab_fst hz).1.le

/-- `lowSlab` is measurable. -/
private lemma measurableSet_lowSlab (a b p q r t : ℝ) : MeasurableSet (lowSlab a b p q r t) :=
  measurableSet_regionBetween (by fun_prop) (by fun_prop) measurableSet_Ioo

/-- An affine function that is nonnegative at both ends of an interval is nonnegative on it
(stated for the difference of two affine functions). -/
private lemma affine_le_of_ends {a b x p q r t : ℝ} (hab : a < b) (hxa : a ≤ x) (hxb : x ≤ b)
    (ha : p * a + q ≤ r * a + t) (hb : p * b + q ≤ r * b + t) : p * x + q ≤ r * x + t := by
  nlinarith [mul_nonneg (sub_nonneg.2 hxa) (sub_nonneg.2 hb),
    mul_nonneg (sub_nonneg.2 hxb) (sub_nonneg.2 ha)]

/-- The integral of the difference of two affine functions. -/
private lemma integral_affine (a b p q r t : ℝ) :
    ∫ x in a..b, ((fun x => r * x + t) - (fun x => p * x + q)) x =
      (r - p) * (b ^ 2 - a ^ 2) / 2 + (t - q) * (b - a) := by
  have : ((fun x : ℝ => r * x + t) - (fun x => p * x + q)) = fun x => (r - p) * x + (t - q) := by
    funext x; simp only [Pi.sub_apply]; ring
  rw [this, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const]
  · simp only [smul_eq_mul]; ring
  · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
  · exact continuous_const.intervalIntegrable _ _

/-- The area of a trapezoid `upSlab`. -/
private lemma vol_up {a b p q r t : ℝ} (hab : a < b)
    (ha : p * a + q ≤ r * a + t) (hb : p * b + q ≤ r * b + t) :
    volume (upSlab a b p q r t) =
      ENNReal.ofReal ((r - p) * (b ^ 2 - a ^ 2) / 2 + (t - q) * (b - a)) := by
  rw [upSlab, Measure.volume_eq_prod, volume_regionBetween_eq_integral
    (Continuous.integrableOn_Icc (by fun_prop)) (Continuous.integrableOn_Icc (by fun_prop))
    measurableSet_Icc (fun x hx => affine_le_of_ends hab hx.1 hx.2 ha hb),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le, integral_affine]

/-- The area of a trapezoid `lowSlab`. -/
private lemma vol_low {a b p q r t : ℝ} (hab : a < b)
    (ha : p * a + q ≤ r * a + t) (hb : p * b + q ≤ r * b + t) :
    volume (lowSlab a b p q r t) =
      ENNReal.ofReal ((r - p) * (b ^ 2 - a ^ 2) / 2 + (t - q) * (b - a)) := by
  rw [lowSlab, Measure.volume_eq_prod, volume_regionBetween_eq_integral
    ((Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self)
    ((Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self)
    measurableSet_Ioo (fun x hx => affine_le_of_ends hab hx.1.le hx.2.le ha hb),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le, integral_affine]

/-- A trapezoid `lowSlab` whose four corners lie in a convex set `K` lies in `K`. -/
private lemma lowSlab_subset {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) {a b p q r t : ℝ}
    (hab : a < b)
    (h1 : (a, p * a + q) ∈ K) (h2 : (b, p * b + q) ∈ K) (h3 : (a, r * a + t) ∈ K)
    (h4 : (b, r * b + t) ∈ K) : lowSlab a b p q r t ⊆ K := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [mem_Ioo] at hx hy
  have hba : 0 < b - a := sub_pos.2 hab
  have hL : ((x : ℝ), p * x + q) ∈ K := by
    have := hK h1 h2 (a := (b - x) / (b - a)) (b := (x - a) / (b - a))
      (div_nonneg (by linarith) hba.le) (div_nonneg (by linarith) hba.le)
      (by field_simp; ring)
    convert this using 1
    ext <;> simp <;> field_simp <;> ring
  have hU : ((x : ℝ), r * x + t) ∈ K := by
    have := hK h3 h4 (a := (b - x) / (b - a)) (b := (x - a) / (b - a))
      (div_nonneg (by linarith) hba.le) (div_nonneg (by linarith) hba.le)
      (by field_simp; ring)
    convert this using 1
    ext <;> simp <;> field_simp <;> ring
  have hd : 0 < r * x + t - (p * x + q) := by linarith
  set D := r * x + t - (p * x + q) with hD
  have hs : (y - (p * x + q)) / D * D = y - (p * x + q) := div_mul_cancel₀ _ hd.ne'
  have hs0 : 0 ≤ (y - (p * x + q)) / D := div_nonneg (by linarith) hd.le
  have hs1 : (y - (p * x + q)) / D ≤ 1 := (div_le_one hd).2 (by linarith)
  have := hK hL hU (a := 1 - (y - (p * x + q)) / D) (b := (y - (p * x + q)) / D)
    (by linarith) hs0 (by ring)
  convert this using 1
  ext
  · simp; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination (-1 : ℝ) * hs

/-- Subadditivity of the volume, in the form used for the upper bound. -/
private lemma le_add_of_union {s T : Set (ℝ × ℝ)} {x y : ENNReal} (hs : volume s ≤ x)
    (hT : volume T ≤ y) : volume (s ∪ T) ≤ x + y :=
  (measure_union_le s T).trans (add_le_add hs hT)

/-- Additivity of the volume for a trapezoid `lowSlab a b …` and a measurable set to its right. -/
private lemma vol_union_lowSlab {a b p q r t : ℝ} {T : Set (ℝ × ℝ)} (hT : MeasurableSet T)
    (hTb : T ⊆ {z | b ≤ z.1}) :
    volume (lowSlab a b p q r t ∪ T) = volume (lowSlab a b p q r t) + volume T := by
  refine measure_union (Set.disjoint_left.2 fun z hz hz' => ?_) hT
  have h1 := (lowSlab_fst hz).2
  have h2 : b ≤ z.1 := hTb hz'
  linarith


/-- The intersection of the closed half-planes `α x + β y ≤ γ` for `(α, β, γ) ∈ H`. -/
private def HP (H : List (ℤ × ℤ × ℤ)) : Set (ℝ × ℝ) :=
  {z | ∀ h ∈ H, (h.1 : ℝ) * z.1 + (h.2.1 : ℝ) * z.2 ≤ (h.2.2 : ℝ)}

/-- An intersection of half-planes is convex. -/
private lemma convex_HP (H : List (ℤ × ℤ × ℤ)) : Convex ℝ (HP H) := by
  intro z hz w hw a b ha hb hab h hh
  have h1 := hz h hh
  have h2 := hw h hh
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have e : (h.2.2 : ℝ) = a * h.2.2 + b * h.2.2 := by rw [← add_mul, hab, one_mul]
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- The twelve edge half-planes of the 12-gon with vertices `(±7, 0), (±6, ±3), (±3, ±6), (0, ±7)`,
the convex hull of the grid points in the disk of radius `7` around the origin. -/
private def H0 : List (ℤ × ℤ × ℤ) :=
  [(-3, -1, 21), (-1, -1, 9), (-1, -3, 21), (1, -3, 21), (1, -1, 9), (3, -1, 21),
   (-3, 1, 21), (-1, 1, 9), (-1, 3, 21), (1, 3, 21), (1, 1, 9), (3, 1, 21)]

/-- Finite check: every grid point in the disk of radius `7` around the origin satisfies the
twelve inequalities of `H0`. -/
private lemma check0 : ∀ i : ℕ, i < 15 → ∀ j : ℕ, j < 15 →
    ((i : ℤ) - 7) ^ 2 + ((j : ℤ) - 7) ^ 2 ≤ 49 →
      ∀ h ∈ H0, h.1 * ((i : ℤ) - 7) + h.2.1 * ((j : ℤ) - 7) ≤ h.2.2 := by
  decide +kernel

/-- `check0` restated for arbitrary integers `x, y` with `x² + y² ≤ 49`. -/
private lemma int_check0 (x y : ℤ) (hxy : x ^ 2 + y ^ 2 ≤ 49) :
    ∀ h ∈ H0, h.1 * x + h.2.1 * y ≤ h.2.2 := by
  have hx1 : -7 ≤ x := by nlinarith
  have hx2 : x ≤ 7 := by nlinarith
  have hy1 : -7 ≤ y := by nlinarith
  have hy2 : y ≤ 7 := by nlinarith
  have := check0 (x + 7).toNat (by omega) (y + 7).toNat (by omega)
  have ex : (((x + 7).toNat : ℕ) : ℤ) - 7 = x := by omega
  have ey : (((y + 7).toNat : ℕ) : ℤ) - 7 = y := by omega
  rw [ex, ey] at this
  exact this hxy

/-- The grid points in the disk of radius `7` around the origin lie in the 12-gon `HP H0`. -/
private lemma disk0_subset : latticeDisk 0 ((7 : ℕ) : ℝ) ⊆ HP H0 := by
  rintro z ⟨x, y, rfl, hxy⟩ h hh
  have hxy' : x ^ 2 + y ^ 2 ≤ 49 := by
    norm_num at hxy
    exact_mod_cast hxy
  have := int_check0 x y hxy' h hh
  simp only
  exact_mod_cast this

/-- The non-lattice center. -/
private noncomputable def c0 : ℝ × ℝ := (5 / 12, 5 / 24)

/-- A grid point in the disk of radius `7` around `c0` lies in the convex hull of all of them. -/
private lemma mem_hull_c0 {u v : ℝ} (x y : ℤ) (hu : u = x) (hv : v = y)
    (hd : ((x : ℝ) - 5 / 12) ^ 2 + ((y : ℝ) - 5 / 24) ^ 2 ≤ 49) :
    (u, v) ∈ convexHull ℝ (latticeDisk c0 ((7 : ℕ) : ℝ)) := by
  apply subset_convexHull
  refine ⟨x, y, by rw [hu, hv], ?_⟩
  simp only [c0]
  norm_num
  linarith


/-- Six slightly thickened trapezoids covering the convex hull of the lattice points in the disk of
radius `7` around the origin. -/
private def U0 : Set (ℝ × ℝ) :=
  upSlab (-7) (-6) (-3) (-2101/100) 3 (2101/100) ∪
    (upSlab (-6) (-3) (-1) (-901/100) 1 (901/100) ∪
    (upSlab (-3) 0 (-1/3) (-701/100) (1/3) (701/100) ∪
    (upSlab 0 3 (1/3) (-701/100) (-1/3) (701/100) ∪
    (upSlab 3 6 1 (-901/100) (-1) (901/100) ∪
    (upSlab 6 7 3 (-2101/100) (-3) (2101/100))))))

/-- Eleven column trapezoids, all of whose corners are lattice points in the disk of radius `7`
around `c0`. -/
private def L0 : Set (ℝ × ℝ) :=
  lowSlab (-6) (-5) (-2) (-14) 1 9 ∪
    (lowSlab (-5) (-4) (-1) (-9) 1 9 ∪
    (lowSlab (-4) (-3) 0 (-5) 1 9 ∪
    (lowSlab (-3) (-2) (-1) (-8) 0 6 ∪
    (lowSlab (-2) (-1) 0 (-6) 1 8 ∪
    (lowSlab (-1) 2 0 (-6) 0 7 ∪
    (lowSlab 2 3 0 (-6) (-1) 9 ∪
    (lowSlab 3 4 1 (-9) 0 6 ∪
    (lowSlab 4 5 0 (-5) (-1) 10 ∪
    (lowSlab 5 6 1 (-10) (-1) 10 ∪
    (lowSlab 6 7 2 (-16) (-2) 16))))))))))

/-- The polygon `HP H0` lies in the union of the six thickened trapezoids. -/
private lemma HP_subset_U0 : HP H0 ⊆ U0 := by
  intro z hz
  have h1 := hz (-3, -1, 21) (by simp [H0])
  have h2 := hz (-1, -1, 9) (by simp [H0])
  have h3 := hz (-1, -3, 21) (by simp [H0])
  have h4 := hz (1, -3, 21) (by simp [H0])
  have h5 := hz (1, -1, 9) (by simp [H0])
  have h6 := hz (3, -1, 21) (by simp [H0])
  have h7 := hz (-3, 1, 21) (by simp [H0])
  have h8 := hz (-1, 1, 9) (by simp [H0])
  have h9 := hz (-1, 3, 21) (by simp [H0])
  have h10 := hz (1, 3, 21) (by simp [H0])
  have h11 := hz (1, 1, 9) (by simp [H0])
  have h12 := hz (3, 1, 21) (by simp [H0])
  push_cast at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  unfold U0
  rcases le_or_gt z.1 (-6) with hx0 | hx0
  · exact Or.inl <| mem_upSlab (by linarith) (by linarith) (by linarith) (by linarith)
  rcases le_or_gt z.1 (-3) with hx1 | hx1
  · exact Or.inr <| Or.inl <| mem_upSlab (by linarith) (by linarith) (by linarith) (by linarith)
  rcases le_or_gt z.1 0 with hx2 | hx2
  · exact Or.inr <| Or.inr <| Or.inl <|
      mem_upSlab (by linarith) (by linarith) (by linarith) (by linarith)
  rcases le_or_gt z.1 3 with hx3 | hx3
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      mem_upSlab (by linarith) (by linarith) (by linarith) (by linarith)
  rcases le_or_gt z.1 6 with hx4 | hx4
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      mem_upSlab (by linarith) (by linarith) (by linarith) (by linarith)
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      mem_upSlab (by linarith) (by linarith) (by linarith) (by linarith)

/-- The volume of `U0` is at most `3457/25 = 138.28`. -/
private lemma vol_U0 : volume U0 ≤ ENNReal.ofReal (3457 / 25) := by
  unfold U0
  have v0 : volume (upSlab (-7) (-6) (-3) (-2101/100) 3 (2101/100)) = ENNReal.ofReal (151/50) := by
    rw [vol_up] <;> norm_num
  have v1 : volume (upSlab (-6) (-3) (-1) (-901/100) 1 (901/100)) = ENNReal.ofReal (1353/50) := by
    rw [vol_up] <;> norm_num
  have v2 : volume (upSlab (-3) 0 (-1/3) (-701/100) (1/3) (701/100)) =
      ENNReal.ofReal (1953/50) := by
    rw [vol_up] <;> norm_num
  have v3 : volume (upSlab 0 3 (1/3) (-701/100) (-1/3) (701/100)) = ENNReal.ofReal (1953/50) := by
    rw [vol_up] <;> norm_num
  have v4 : volume (upSlab 3 6 1 (-901/100) (-1) (901/100)) = ENNReal.ofReal (1353/50) := by
    rw [vol_up] <;> norm_num
  have v5 : volume (upSlab 6 7 3 (-2101/100) (-3) (2101/100)) = ENNReal.ofReal (151/50) := by
    rw [vol_up] <;> norm_num
  refine le_trans (le_add_of_union v0.le (le_add_of_union v1.le (le_add_of_union v2.le
    (le_add_of_union v3.le (le_add_of_union v4.le v5.le))))) ?_
  repeat rw [← ENNReal.ofReal_add]
  · exact ENNReal.ofReal_le_ofReal (by norm_num)
  all_goals norm_num

/-- The eleven trapezoids lie in the convex hull of the lattice points in the disk around `c0`. -/
private lemma L0_subset : L0 ⊆ convexHull ℝ (latticeDisk c0 ((7 : ℕ) : ℝ)) := by
  unfold L0
  refine union_subset ?_ ?_
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (-6) (-2) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-5) (-4) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-6) (3) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-5) (4) (by norm_num) (by norm_num) (by norm_num))
  refine union_subset ?_ ?_
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (-5) (-4) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-4) (-5) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-5) (4) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-4) (5) (by norm_num) (by norm_num) (by norm_num))
  refine union_subset ?_ ?_
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (-4) (-5) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-3) (-5) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-4) (5) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-3) (6) (by norm_num) (by norm_num) (by norm_num))
  refine union_subset ?_ ?_
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (-3) (-5) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-2) (-6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-3) (6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-2) (6) (by norm_num) (by norm_num) (by norm_num))
  refine union_subset ?_ ?_
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (-2) (-6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-1) (-6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-2) (6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-1) (7) (by norm_num) (by norm_num) (by norm_num))
  refine union_subset ?_ ?_
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (-1) (-6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (2) (-6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (-1) (7) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (2) (7) (by norm_num) (by norm_num) (by norm_num))
  refine union_subset ?_ ?_
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (2) (-6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (3) (-6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (2) (7) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (3) (6) (by norm_num) (by norm_num) (by norm_num))
  refine union_subset ?_ ?_
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (3) (-6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (4) (-5) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (3) (6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (4) (6) (by norm_num) (by norm_num) (by norm_num))
  refine union_subset ?_ ?_
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (4) (-5) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (5) (-5) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (4) (6) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (5) (5) (by norm_num) (by norm_num) (by norm_num))
  refine union_subset ?_ ?_
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (5) (-5) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (6) (-4) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (5) (5) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (6) (4) (by norm_num) (by norm_num) (by norm_num))
  · exact lowSlab_subset (convex_convexHull ℝ _) (by norm_num)
      (mem_hull_c0 (6) (-4) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (7) (-2) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (6) (4) (by norm_num) (by norm_num) (by norm_num))
      (mem_hull_c0 (7) (2) (by norm_num) (by norm_num) (by norm_num))

/-- The volume of `L0` is `277/2 = 138.5`. -/
private lemma vol_L0 : volume L0 = ENNReal.ofReal (277 / 2) := by
  unfold L0
  have v0 : volume (lowSlab (-6) (-5) (-2) (-14) 1 9) = ENNReal.ofReal (13/2) := by
    rw [vol_low] <;> norm_num
  have v1 : volume (lowSlab (-5) (-4) (-1) (-9) 1 9) = ENNReal.ofReal 9 := by
    rw [vol_low] <;> norm_num
  have v2 : volume (lowSlab (-4) (-3) 0 (-5) 1 9) = ENNReal.ofReal (21/2) := by
    rw [vol_low] <;> norm_num
  have v3 : volume (lowSlab (-3) (-2) (-1) (-8) 0 6) = ENNReal.ofReal (23/2) := by
    rw [vol_low] <;> norm_num
  have v4 : volume (lowSlab (-2) (-1) 0 (-6) 1 8) = ENNReal.ofReal (25/2) := by
    rw [vol_low] <;> norm_num
  have v5 : volume (lowSlab (-1) 2 0 (-6) 0 7) = ENNReal.ofReal 39 := by
    rw [vol_low] <;> norm_num
  have v6 : volume (lowSlab 2 3 0 (-6) (-1) 9) = ENNReal.ofReal (25/2) := by
    rw [vol_low] <;> norm_num
  have v7 : volume (lowSlab 3 4 1 (-9) 0 6) = ENNReal.ofReal (23/2) := by
    rw [vol_low] <;> norm_num
  have v8 : volume (lowSlab 4 5 0 (-5) (-1) 10) = ENNReal.ofReal (21/2) := by
    rw [vol_low] <;> norm_num
  have v9 : volume (lowSlab 5 6 1 (-10) (-1) 10) = ENNReal.ofReal 9 := by
    rw [vol_low] <;> norm_num
  have v10 : volume (lowSlab 6 7 2 (-16) (-2) 16) = ENNReal.ofReal 6 := by
    rw [vol_low] <;> norm_num
  repeat rw [vol_union_lowSlab]
  · rw [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    repeat rw [← ENNReal.ofReal_add]
    · norm_num
    all_goals norm_num
  all_goals
    repeat' first
      | exact measurableSet_lowSlab _ _ _ _ _ _
      | exact lowSlab_subset_ge (by norm_num)
      | apply MeasurableSet.union
      | apply union_subset

/-- The convex hull of the lattice points in the closed disk of radius `7` around the origin lies
in `U0`. -/
private lemma hull0_subset : convexHull ℝ (latticeDisk 0 ((7 : ℕ) : ℝ)) ⊆ U0 :=
  (convexHull_min disk0_subset (convex_HP H0)).trans HP_subset_U0

/-- The conjecture fails at `n = 7`: with the center `c0 = (5/12, 5/24)` the convex hull of the
lattice points in the disk of radius `7` has area at least `277/2`, while with a lattice center
it has area at most `3457/25 < 277/2` (in fact exactly `138`). -/
theorem result : ¬ statement := by
  intro h
  have h7 := h 7
  have hlt : maxArea 0 ((7 : ℕ) : ℝ) < maxArea c0 ((7 : ℕ) : ℝ) := by
    unfold maxArea
    calc volume (convexHull ℝ (latticeDisk 0 ((7 : ℕ) : ℝ))) ≤ volume U0 :=
          measure_mono hull0_subset
      _ ≤ ENNReal.ofReal (3457 / 25) := vol_U0
      _ < ENNReal.ofReal (277 / 2) := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
      _ = volume L0 := vol_L0.symm
      _ ≤ volume (convexHull ℝ (latticeDisk c0 ((7 : ℕ) : ℝ))) := measure_mono L0_subset
  have hle : maxArea c0 ((7 : ℕ) : ℝ) ≤ ⨆ c, maxArea c ((7 : ℕ) : ℝ) :=
    le_iSup (fun c => maxArea c ((7 : ℕ) : ℝ)) c0
  rw [h7] at hle
  exact absurd hle (not_le.2 hlt)

end Math0.Frontier.A386538

#math0_settles Math0.Frontier.A386538.result Math0.Statements.A386538.statement
