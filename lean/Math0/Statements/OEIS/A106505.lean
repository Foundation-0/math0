/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A106505: side common to angles `A` and `2A` in primitive integer triangles

Source: https://oeis.org/A106505, Ralf Stephan, Nov 16 2010 (FORMULA section). Verbatim:
> Conjecture: for n>2, a(n+5) = a(n) + 8.

The entry (Lekraj Beedassy, May 04 2005, offset `1`) is "Ordered and uniqued length of side
common to the two angles, one being the double of the other, of a primitive integer-sided
triangle." Data: `5, 7, 9, 11, 13, 15, 16, 17, 19, 21, 23, 24, 25, …, 111, 112`.

## Encoding

* *Angles of a triangle.* For a triangle with side lengths `p, q, r`, the angle opposite the side
  `p` is `arccos ((q² + r² - p²) / (2 q r))` (law of cosines; this is the unoriented angle in
  `[0, π]`, as for `EuclideanGeometry.angle`). This is `angleOpp p q r`.
* *Triangles with one angle the double of another.* `IsDoubleAngleTriangle x y c`: the natural
  numbers `x, y, c` satisfy the strict triangle inequalities (a non-degenerate triangle; this
  forces `x, y, c ≥ 1`), and the angle opposite `y` is twice the angle opposite `x`. The side
  `c` joins the vertices of these two angles, so it is the side common to them. Every triangle
  with two angles, one the double of the other, arises this way (name the side opposite the
  smaller angle `x`, the side opposite the larger one `y`).
* *Primitive.* `gcd(x, y, c) = 1`.
* `IsSide c`: there are `x, y` with `IsDoubleAngleTriangle x y c` and `gcd(x, y, c) = 1`.
  "Ordered and uniqued": `a n = Nat.nth IsSide (n - 1)` is the `n`-th smallest element of
  `{c | IsSide c}` (offset `1`), noncomputable as written.
* *Decidability.* `isDoubleAngleTriangle_iff` proves (via the double-angle formula
  `cos 2α = 2 cos² α - 1`) that the angle condition is equivalent to the classical metric
  relation `y² = x (x + c)`. Writing `y = x + d`, this becomes `x (c - 2d) = d²` with
  `0 < d`, `2d < c`, so `x` is determined by `d < c` (`isSide_iff`). This gives a
  `DecidablePred IsSide` instance, and `a_data` checks all 67 listed terms (all members
  `< 113`) by a kernel-checked `List.filter`. (The entry's formula "Values s^2 - r^2, where
  r<s<2r and (r, s)=1" is not used.)
* *The conjecture.* `statement`: `a (n + 5) = a n + 8` for every `n > 2` (`n` is 1-indexed as in
  the entry; it fails for `n = 1, 2`).
-/

namespace Math0.Statements.A106505

/-! ### Definitions -/

/-- The angle opposite the side of length `p` in a triangle with side lengths `p, q, r`, by the
law of cosines: `arccos ((q² + r² - p²) / (2 q r))`. -/
noncomputable def angleOpp (p q r : ℝ) : ℝ :=
  Real.arccos ((q ^ 2 + r ^ 2 - p ^ 2) / (2 * q * r))

/-- `x, y, c` are the side lengths of a non-degenerate triangle in which the angle opposite `y`
is twice the angle opposite `x`. The side `c` is the side common to these two angles. -/
def IsDoubleAngleTriangle (x y c : ℕ) : Prop :=
  x < y + c ∧ y < x + c ∧ c < x + y ∧
    angleOpp (y : ℝ) (x : ℝ) (c : ℝ) = 2 * angleOpp (x : ℝ) (y : ℝ) (c : ℝ)

/-- `c` is the length of the side common to the two angles, one being the double of the other,
of a primitive integer-sided triangle. -/
def IsSide (c : ℕ) : Prop :=
  ∃ x y : ℕ, IsDoubleAngleTriangle x y c ∧ Nat.gcd (Nat.gcd x y) c = 1

/-! ### Decidability -/

/-- For a non-degenerate triangle, the angle opposite `y` is twice the angle opposite `x` iff
`y² = x (x + c)`. -/
theorem isDoubleAngleTriangle_iff (x y c : ℕ) :
    IsDoubleAngleTriangle x y c ↔
      x < y + c ∧ y < x + c ∧ c < x + y ∧ y * y = x * (x + c) := by
  unfold IsDoubleAngleTriangle
  refine and_congr_right fun h1 => and_congr_right fun h2 => and_congr_right fun h3 => ?_
  have hx : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hy : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hc : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have r1 : (x : ℝ) < y + c := by exact_mod_cast h1
  have r2 : (y : ℝ) < x + c := by exact_mod_cast h2
  have r3 : (c : ℝ) < x + y := by exact_mod_cast h3
  have hcast : y * y = x * (x + c) ↔ (y : ℝ) * y = x * (x + c) := by
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  rw [hcast]
  unfold angleOpp
  generalize (x : ℝ) = X at *
  generalize (y : ℝ) = Y at *
  generalize (c : ℝ) = C at *
  have hu1 : -1 ≤ (X ^ 2 + C ^ 2 - Y ^ 2) / (2 * X * C) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hu2 : (X ^ 2 + C ^ 2 - Y ^ 2) / (2 * X * C) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hv1 : -1 ≤ (Y ^ 2 + C ^ 2 - X ^ 2) / (2 * Y * C) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hv2 : (Y ^ 2 + C ^ 2 - X ^ 2) / (2 * Y * C) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  constructor
  · intro h
    have h' := congrArg Real.cos h
    rw [Real.cos_arccos hu1 hu2, Real.cos_two_mul, Real.cos_arccos hv1 hv2] at h'
    field_simp at h'
    have key : (C + X) * (X - Y - C) * (X + Y - C) * (C * X + X ^ 2 - Y ^ 2) = 0 := by
      linear_combination -h'
    have hA : (C + X) * (X - Y - C) * (X + Y - C) ≠ 0 := by
      have : (C + X) * (X - Y - C) * (X + Y - C) < 0 := by
        have h4 : 0 < (C + X) * (X + Y - C) := by nlinarith
        nlinarith
      exact this.ne
    have := (mul_eq_zero.1 key).resolve_left hA
    linear_combination -this
  · intro h
    have hv0 : 0 ≤ (Y ^ 2 + C ^ 2 - X ^ 2) / (2 * Y * C) := by
      apply div_nonneg _ (by positivity)
      nlinarith
    have hcos : (X ^ 2 + C ^ 2 - Y ^ 2) / (2 * X * C) =
        Real.cos (2 * Real.arccos ((Y ^ 2 + C ^ 2 - X ^ 2) / (2 * Y * C))) := by
      rw [Real.cos_two_mul, Real.cos_arccos hv1 hv2]
      field_simp
      linear_combination (C + X) * (X - Y - C) * (X + Y - C) * h
    rw [hcos, Real.arccos_cos
      (by linarith [Real.arccos_nonneg ((Y ^ 2 + C ^ 2 - X ^ 2) / (2 * Y * C))])
      (by linarith [Real.arccos_le_pi_div_two.2 hv0])]

/-- `IsSide c` is decided by a search over `d = y - x < c`: then `x = d² / (c - 2d)`. -/
theorem isSide_iff (c : ℕ) : IsSide c ↔
    ∃ d < c, 0 < d ∧ 2 * d < c ∧ d * d % (c - 2 * d) = 0 ∧
      c < d * d / (c - 2 * d) + (d * d / (c - 2 * d) + d) ∧
      Nat.gcd (Nat.gcd (d * d / (c - 2 * d)) (d * d / (c - 2 * d) + d)) c = 1 := by
  constructor
  · rintro ⟨x, y, h, hg⟩
    obtain ⟨h1, h2, h3, hyy⟩ := (isDoubleAngleTriangle_iff x y c).1 h
    have hx : 0 < x := by omega
    have hc : 0 < c := by omega
    have hxy : x < y := by
      by_contra hle
      replace hle : y ≤ x := by omega
      have := Nat.mul_le_mul hle hle
      have : x * x < x * (x + c) := Nat.mul_lt_mul_of_pos_left (by omega) hx
      omega
    obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
    have hd : 0 < d := by omega
    have hrel : x * c = x * (2 * d) + d * d := by
      have : (x + d) * (x + d) = x * x + x * (2 * d) + d * d := by ring
      have : x * (x + c) = x * x + x * c := by ring
      omega
    have h2d : 2 * d < c := by
      have : x * (2 * d) < x * c := by
        have : 0 < d * d := Nat.mul_pos hd hd
        omega
      exact Nat.lt_of_mul_lt_mul_left this
    have hdd : d * d = (c - 2 * d) * x := by
      rw [Nat.sub_mul, Nat.mul_comm c x, Nat.mul_comm (2 * d) x]
      omega
    have hpos : 0 < c - 2 * d := by omega
    have hdiv : d * d / (c - 2 * d) = x := by
      rw [hdd, Nat.mul_div_cancel_left _ hpos]
    refine ⟨d, by omega, hd, h2d, ?_, ?_, ?_⟩
    · rw [hdd, Nat.mul_mod_right]
    · rw [hdiv]; omega
    · rw [hdiv]; exact hg
  · rintro ⟨d, -, hd, h2d, hmod, h3, hg⟩
    set x := d * d / (c - 2 * d) with hxdef
    have hpos : 0 < c - 2 * d := by omega
    have hx : x * (c - 2 * d) = d * d := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
    refine ⟨x, x + d, (isDoubleAngleTriangle_iff _ _ _).2 ⟨by omega, by omega, h3, ?_⟩, hg⟩
    have hsub : ((c - 2 * d : ℕ) : ℤ) = (c : ℤ) - 2 * d := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hxz : (x : ℤ) * ((c : ℤ) - 2 * d) = (d : ℤ) * d := by
      rw [← hsub]; exact_mod_cast hx
    have : ((x + d : ℕ) : ℤ) * (x + d : ℕ) = (x : ℤ) * ((x + c : ℕ) : ℤ) := by
      push_cast
      linear_combination -hxz
    exact_mod_cast this

instance : DecidablePred IsSide := fun c => decidable_of_iff _ (isSide_iff c).symm

/-! ### The sequence -/

/-- A106505: the `n`-th smallest (offset `1`) length of the side common to the two angles, one
being the double of the other, of a primitive integer-sided triangle. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsSide (n - 1)

/-- The elements `< N` satisfying `p`, in increasing order, are `nth p 0, nth p 1, …`. -/
theorem filter_range_eq (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    (List.range N).filter (fun k => decide (p k)) =
      (List.range (Nat.count p N)).map (Nat.nth p) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, ih, Nat.count_succ]
    by_cases h : p N
    · simp [h, List.range_succ, Nat.nth_count h]
    · simp [h]

theorem map_nth_eq_of_filter {p : ℕ → Prop} [DecidablePred p] {N K : ℕ} {L : List ℕ}
    (h : (List.range N).filter (fun k => decide (p k)) = L) (hK : L.length = K) :
    (List.range K).map (Nat.nth p) = L := by
  rw [filter_range_eq] at h
  subst h
  simp only [List.length_map, List.length_range] at hK
  rw [hK]

/-- The entry's example: `(x, y, c) = (16, 28, 33)` and `(256, 272, 33)` are two primitive
triangles in which the angle opposite `y` is twice the angle opposite `x`, both with common
side `33` (the entry lists the sides as `(33, 28, 16)` and `(33, 272, 256)`). -/
theorem example_33 :
    IsDoubleAngleTriangle 16 28 33 ∧ IsDoubleAngleTriangle 256 272 33 := by
  rw [isDoubleAngleTriangle_iff, isDoubleAngleTriangle_iff]
  decide

/-- The definition reproduces all 67 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 67).map (fun i => a (i + 1)) =
    [5, 7, 9, 11, 13, 15, 16, 17, 19, 21, 23, 24, 25, 27, 29, 31, 32, 33, 35, 37, 39, 40, 41, 43,
      45, 47, 48, 49, 51, 53, 55, 56, 57, 59, 61, 63, 64, 65, 67, 69, 71, 72, 73, 75, 77, 79, 80,
      81, 83, 85, 87, 88, 89, 91, 93, 95, 96, 97, 99, 101, 103, 104, 105, 107, 109, 111, 112] := by
  have : (fun i => a (i + 1)) = Nat.nth IsSide := funext fun i => by simp [a]
  rw [this]
  exact map_nth_eq_of_filter (N := 113) (by decide +kernel) rfl

/-! ### The conjecture -/

/-- Conjecture (Stephan, A106505): for `n > 2`, `a(n + 5) = a(n) + 8`. -/
def statement : Prop := ∀ n : ℕ, 2 < n → a (n + 5) = a n + 8

end Math0.Statements.A106505
