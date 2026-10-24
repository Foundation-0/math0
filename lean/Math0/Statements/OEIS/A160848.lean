/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A160848: Barker's order-20 recurrence for the lines through an `8 × n` grid

Source: https://oeis.org/A160848, _Colin Barker_, Dec 25 2017 (FORMULA section). Verbatim:
> Conjectures from _Colin Barker_, Dec 25 2017: (Start)
>
> G.f.: x*(1 + 66*x + 132*x^2 + 304*x^3 + 492*x^4 + 771*x^5 + 1003*x^6 + 1273*x^7 + 1390*x^8 +
> 1480*x^9 + 1374*x^10 + 1241*x^11 + 971*x^12 + 739*x^13 + 476*x^14 + 296*x^15 + 140*x^16 +
> 74*x^17 + 17*x^18 + 8*x^19 + 8*x^20) / ((1 - x)^3*(1 + x)*(1 - x + x^2)*(1 + x^2)*(1 + x + x^2)*
> (1 + x + x^2 + x^3 + x^4)*(1 + x + x^2 + x^3 + x^4 + x^5 + x^6)).
>
> a(n) = -a(n-2) + a(n-5) + a(n-6) + 2*a(n-7) + a(n-8) + a(n-9) - a(n-11) - a(n-12) - 2*a(n-13)
> - a(n-14) - a(n-15) + a(n-18) + a(n-20) for n>21.
>
> (End)

The sequence (_Seppo Mustonen_, May 28 2009, offset `0`) is "Number of lines through at least 2
points of an 8 X n grid of points."

## Encoding

* *The grid.* The `8 × n` grid of points is `{0, …, n-1} × {0, …, 7} ⊆ ℤ²` (the transposed grid
  `{0, …, 7} × {0, …, n-1}` is congruent to it, so it has the same number of lines). Its points
  are numbered `0, …, 8n-1`: the point with number `i` is `pt i = (i / 8, i % 8)`, and this is a
  bijection from `{0, …, 8n-1}` onto the grid. For `n = 0` the grid is empty.
* *Lines.* For two distinct points `p ≠ q` of `ℤ²`, a point `r` lies on the line `pq` iff
  `Collinear3 p q r`, i.e. `(q - p) × (r - p) = 0`. A line of the plane containing at least two
  grid points `p ≠ q` is the line `pq`. Two distinct lines have at most one common point, so such
  a line is determined by the set of grid points on it, and conversely. Hence the number of lines
  through at least two grid points is the number of distinct sets
  `lineThrough n i j = {k < 8n | pt k lies on the line through pt i and pt j}` with `i ≠ j`,
  `i, j < 8n`. This is the definition of `a n` (a cardinality of a computable `Finset`).
* *Fast evaluation (proved equal).* Each line is counted once by its two smallest grid points in
  the numbering (`IsFirst`, `a_eq_card_firstPairs`; this uses only that two distinct grid points
  of a line span it, `collinear_iff`). For `i < j`, the pair `(pt i, pt j)` consists of the two
  smallest grid points on its line iff `d = pt j - pt i` is primitive (`gcd = 1`) and
  `pt i - d` is not a grid point (`isFirst_iff`). This gives the `O((8n)²)` count `aFast`, and
  `a_eq_aFast` proves `a n = aFast n` for every `n`.
* *Data.* `a_data` checks all 41 listed terms `a(0), …, a(40)` in the kernel (via `a_eq_aFast`).
  `recurrence_data` checks that these values satisfy the conjectured recurrence for
  `22 ≤ n ≤ 40` (a sanity check of the transcription of the recurrence, not a proof).
* *The conjecture.* `statement` is the recurrence, for every `n > 21` exactly as in the entry
  (`Recurrence`). The values are taken in `ℤ` because of the negative coefficients; for
  `n > 21` every index `n - k` (`k ≤ 20`) is at least `2`, so the natural-number subtractions are
  exact. The g.f. conjecture is recorded separately as `statement_gf`: the identity
  `A(x) · D(x) = x · N(x)` of formal power series over `ℤ`, where `A(x) = ∑ a(n) xⁿ`, `D` is the
  stated denominator and `x · N(x)` the stated numerator; since `D(0) = 1`, this is the same as
  `A(x) = x · N(x) / D(x)`. (`D(x) = 1 + x² - x⁵ - x⁶ - 2x⁷ - x⁸ - x⁹ + x¹¹ + x¹² + 2x¹³ + x¹⁴
  + x¹⁵ - x¹⁸ - x²⁰` is the characteristic polynomial of the recurrence, so `statement_gf` is
  equivalent to `statement` together with the agreement of the first 22 coefficients.)
-/

namespace Math0.Statements.A160848

/-! ### The sequence -/

/-- The grid point with number `i`: column `i / 8`, row `i % 8`. The numbers `i < 8 * n` give
each point of the `8 × n` grid `{0, …, n-1} × {0, …, 7}` exactly once. -/
def pt (i : ℕ) : ℤ × ℤ := (((i / 8 : ℕ) : ℤ), ((i % 8 : ℕ) : ℤ))

/-- `p`, `q`, `r` are collinear: `(q - p) × (r - p) = 0`. For `p ≠ q` this says that `r` lies on
the line through `p` and `q`. -/
def Collinear3 (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

instance (p q r : ℤ × ℤ) : Decidable (Collinear3 p q r) :=
  inferInstanceAs (Decidable (_ = _))

/-- The (numbers of the) points of the `8 × n` grid on the line through `pt i` and `pt j`. -/
def lineThrough (n i j : ℕ) : Finset ℕ :=
  (Finset.range (8 * n)).filter fun k => Collinear3 (pt i) (pt j) (pt k)

/-- A160848: the number of lines through at least 2 points of the `8 × n` grid, i.e. the number of
distinct sets of grid points `lineThrough n i j` cut out by the lines through two distinct grid
points `pt i ≠ pt j`. -/
def a (n : ℕ) : ℕ :=
  (((Finset.range (8 * n) ×ˢ Finset.range (8 * n)).filter fun ij => ij.1 ≠ ij.2).image
    fun ij => lineThrough n ij.1 ij.2).card

/-! ### Fast evaluation of `a` -/

/-- `pt` is injective. -/
theorem pt_injective {i j : ℕ} (h : pt i = pt j) : i = j := by
  simp only [pt, Prod.mk.injEq, Nat.cast_inj] at h
  omega

theorem collinear_left (p q : ℤ × ℤ) : Collinear3 p q p := by
  simp [Collinear3]

theorem collinear_right (p q : ℤ × ℤ) : Collinear3 p q q := by
  simp only [Collinear3]; ring

/-- Two distinct points `u ≠ w` on the line through `p ≠ q` span the same line. -/
theorem collinear_iff {p q u w r : ℤ × ℤ} (hpq : p ≠ q) (huw : u ≠ w)
    (hu : Collinear3 p q u) (hw : Collinear3 p q w) :
    Collinear3 u w r ↔ Collinear3 p q r := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨u1, u2⟩ := u
  obtain ⟨w1, w2⟩ := w
  obtain ⟨r1, r2⟩ := r
  simp only [Collinear3, ne_eq, Prod.mk.injEq] at *
  have hv : q1 - p1 ≠ 0 ∨ q2 - p2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hpq ⟨by linarith [h.1], by linarith [h.2]⟩
  have hW : w1 - u1 ≠ 0 ∨ w2 - u2 ≠ 0 := by
    by_contra h
    push Not at h
    exact huw ⟨by linarith [h.1], by linarith [h.2]⟩
  have hX : (w1 - u1) * (u2 - p2) - (w2 - u2) * (u1 - p1) = 0 := by
    rcases hv with hv | hv
    · have e : (q1 - p1) * ((w1 - u1) * (u2 - p2) - (w2 - u2) * (u1 - p1)) = 0 := by
        linear_combination (w1 - p1) * hu - (u1 - p1) * hw
      exact (mul_eq_zero.mp e).resolve_left hv
    · have e : (q2 - p2) * ((w1 - u1) * (u2 - p2) - (w2 - u2) * (u1 - p1)) = 0 := by
        linear_combination (w2 - p2) * hu - (u2 - p2) * hw
      exact (mul_eq_zero.mp e).resolve_left hv
  constructor
  · intro h
    have hWc : (w1 - u1) * (r2 - p2) - (w2 - u2) * (r1 - p1) = 0 := by
      linear_combination h + hX
    have e1 : (w1 - u1) * ((q1 - p1) * (r2 - p2) - (q2 - p2) * (r1 - p1)) = 0 := by
      linear_combination (q1 - p1) * hWc + (r1 - p1) * (hw - hu)
    have e2 : (w2 - u2) * ((q1 - p1) * (r2 - p2) - (q2 - p2) * (r1 - p1)) = 0 := by
      linear_combination (q2 - p2) * hWc + (r2 - p2) * (hw - hu)
    rcases hW with hW | hW
    · linear_combination (mul_eq_zero.mp e1).resolve_left hW
    · linear_combination (mul_eq_zero.mp e2).resolve_left hW
  · intro h
    have e1 : (q1 - p1) * ((w1 - u1) * (r2 - p2) - (w2 - u2) * (r1 - p1)) = 0 := by
      linear_combination (w1 - u1) * h - (r1 - p1) * (hw - hu)
    have e2 : (q2 - p2) * ((w1 - u1) * (r2 - p2) - (w2 - u2) * (r1 - p1)) = 0 := by
      linear_combination (w2 - u2) * h - (r2 - p2) * (hw - hu)
    rcases hv with hv | hv
    · linear_combination (mul_eq_zero.mp e1).resolve_left hv - hX
    · linear_combination (mul_eq_zero.mp e2).resolve_left hv - hX

/-- `IsFirst i j`: no grid point with a number `k < j` other than `i` lies on the line through
`pt i` and `pt j`. -/
def IsFirst (i j : ℕ) : Prop := ∀ k < j, k ≠ i → ¬ Collinear3 (pt i) (pt j) (pt k)

instance (i j : ℕ) : Decidable (IsFirst i j) := by unfold IsFirst; infer_instance

/-- The pairs `⟨j, i⟩` with `i < j < 8n` such that `pt i`, `pt j` are the two smallest grid
points (in the numbering) on their line. -/
def firstPairs (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range (8 * n)).sigma fun j => (Finset.range j).filter fun i => IsFirst i j

theorem mem_lineThrough {n i j k : ℕ} :
    k ∈ lineThrough n i j ↔ k < 8 * n ∧ Collinear3 (pt i) (pt j) (pt k) := by
  simp [lineThrough]

theorem eq_of_mem_of_isFirst {n i j k : ℕ} (hf : IsFirst i j) (hk : k ∈ lineThrough n i j)
    (hkj : k < j) : k = i := by
  by_contra hki
  exact hf k hkj hki (mem_lineThrough.mp hk).2

/-- Every line through at least two grid points is counted exactly once by its two smallest grid
points. -/
theorem a_eq_card_firstPairs (n : ℕ) : a n = (firstPairs n).card := by
  unfold a
  symm
  apply Finset.card_bij (fun x _ => lineThrough n x.2 x.1)
  · intro x hx
    simp only [firstPairs, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx
    rw [Finset.mem_image]
    refine ⟨(x.2, x.1), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  · rintro ⟨j, i⟩ hx ⟨j', i'⟩ hy hxy
    simp only [firstPairs, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx hy
    simp only at hxy
    obtain ⟨hj, hi, hf⟩ := hx
    obtain ⟨hj', hi', hf'⟩ := hy
    have hiS : i ∈ lineThrough n i j :=
      mem_lineThrough.mpr ⟨by omega, collinear_left _ _⟩
    have hjS : j ∈ lineThrough n i j :=
      mem_lineThrough.mpr ⟨hj, collinear_right _ _⟩
    have hi'S : i' ∈ lineThrough n i' j' :=
      mem_lineThrough.mpr ⟨by omega, collinear_left _ _⟩
    have hj'S : j' ∈ lineThrough n i' j' :=
      mem_lineThrough.mpr ⟨hj', collinear_right _ _⟩
    rw [hxy] at hiS hjS
    have hjj : j = j' := by
      rcases lt_trichotomy j j' with h | h | h
      · have e1 := eq_of_mem_of_isFirst hf' hjS h
        have e2 := eq_of_mem_of_isFirst hf' hiS (by omega)
        omega
      · exact h
      · rw [← hxy] at hi'S hj'S
        have e1 := eq_of_mem_of_isFirst hf hj'S h
        have e2 := eq_of_mem_of_isFirst hf hi'S (by omega)
        omega
    subst hjj
    have := eq_of_mem_of_isFirst hf' hiS hi
    subst this
    rfl
  · intro S hS
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hS
    obtain ⟨⟨p, q⟩, ⟨⟨hp, hq⟩, hpq⟩, rfl⟩ := hS
    simp only at hp hq hpq ⊢
    have hpS : p ∈ lineThrough n p q := mem_lineThrough.mpr ⟨hp, collinear_left _ _⟩
    have hqS : q ∈ lineThrough n p q := mem_lineThrough.mpr ⟨hq, collinear_right _ _⟩
    have hne : (lineThrough n p q).Nonempty := ⟨p, hpS⟩
    set S := lineThrough n p q with hSdef
    set i := S.min' hne with hidef
    have hiS : i ∈ S := Finset.min'_mem S hne
    have hne2 : (S.erase i).Nonempty := by
      by_cases hpi : p = i
      · exact ⟨q, Finset.mem_erase.mpr ⟨by omega, hqS⟩⟩
      · exact ⟨p, Finset.mem_erase.mpr ⟨hpi, hpS⟩⟩
    set j := (S.erase i).min' hne2 with hjdef
    have hjS' : j ∈ S.erase i := Finset.min'_mem _ hne2
    have hjS : j ∈ S := Finset.mem_of_mem_erase hjS'
    have hji : j ≠ i := Finset.ne_of_mem_erase hjS'
    have hij : i < j := lt_of_le_of_ne (Finset.min'_le S j hjS) (Ne.symm hji)
    have hmin : ∀ k ∈ S, k ≠ i → j ≤ k := fun k hk hki =>
      Finset.min'_le _ k (Finset.mem_erase.mpr ⟨hki, hk⟩)
    have hjn : j < 8 * n := (mem_lineThrough.mp hjS).1
    have hL : lineThrough n i j = S := by
      ext k
      rw [mem_lineThrough, hSdef, mem_lineThrough]
      have hpq' : pt p ≠ pt q := fun h => hpq (pt_injective h)
      have hij' : pt i ≠ pt j := fun h => hji (pt_injective h).symm
      rw [collinear_iff hpq' hij' (mem_lineThrough.mp hiS).2 (mem_lineThrough.mp hjS).2]
    refine ⟨⟨j, i⟩, ?_, hL⟩
    simp only [firstPairs, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
    refine ⟨hjn, hij, ?_⟩
    intro k hkj hki hcol
    have hkS : k ∈ S := hL ▸ mem_lineThrough.mpr ⟨by omega, hcol⟩
    have := hmin k hkS hki
    omega

/-- Fast test, for `i < j`, of `IsFirst i j` (`isFirst_iff`): with `d = pt j - pt i`,
`gcd(d) = 1` and `pt i - d` is not a grid point. -/
def goodF (i j : ℕ) : Bool :=
  decide (Nat.gcd (j / 8 - i / 8) (j % 8 - i % 8 + (i % 8 - j % 8)) = 1 ∧
    ¬(j / 8 ≤ 2 * (i / 8) ∧ j % 8 ≤ 2 * (i % 8) ∧ 2 * (i % 8) < 8 + j % 8))

theorem goodF_iff (i j : ℕ) : goodF i j = true ↔
    (Nat.gcd (j / 8 - i / 8) (j % 8 - i % 8 + (i % 8 - j % 8)) = 1 ∧
      ¬(j / 8 ≤ 2 * (i / 8) ∧ j % 8 ≤ 2 * (i % 8) ∧ 2 * (i % 8) < 8 + j % 8)) :=
  decide_eq_true_iff

theorem gcd_eq (i j : ℕ) (hxij : i / 8 ≤ j / 8) :
    Nat.gcd (j / 8 - i / 8) (j % 8 - i % 8 + (i % 8 - j % 8)) =
      Int.gcd (((j / 8 : ℕ) : ℤ) - ((i / 8 : ℕ) : ℤ)) (((j % 8 : ℕ) : ℤ) - ((i % 8 : ℕ) : ℤ)) := by
  rw [Int.gcd_eq_natAbs]
  congr 1 <;> omega

theorem gcd_of_isFirst {i j : ℕ} (hij : i < j) (H : IsFirst i j) :
    Int.gcd (((j / 8 : ℕ) : ℤ) - ((i / 8 : ℕ) : ℤ))
      (((j % 8 : ℕ) : ℤ) - ((i % 8 : ℕ) : ℤ)) = 1 := by
  have hji : (j : ℤ) - i = 8 * (((j / 8 : ℕ) : ℤ) - ((i / 8 : ℕ) : ℤ)) +
      (((j % 8 : ℕ) : ℤ) - ((i % 8 : ℕ) : ℤ)) := by omega
  set dx : ℤ := ((j / 8 : ℕ) : ℤ) - ((i / 8 : ℕ) : ℤ) with hdx
  set dy : ℤ := ((j % 8 : ℕ) : ℤ) - ((i % 8 : ℕ) : ℤ) with hdy
  by_contra hg
  have hg0 : Int.gcd dx dy ≠ 0 := by
    rw [Ne, Int.gcd_eq_zero_iff]
    omega
  have hg2 : (2 : ℤ) ≤ (Int.gcd dx dy : ℤ) := by omega
  obtain ⟨A, hA⟩ := Int.gcd_dvd_left (a := dx) (b := dy)
  obtain ⟨B, hB⟩ := Int.gcd_dvd_right (a := dx) (b := dy)
  set g : ℤ := (Int.gcd dx dy : ℤ) with hgdef
  have hdx0 : 0 ≤ dx := by omega
  have hf : g * (8 * A + B) = (j : ℤ) - i := by rw [hji, hA, hB]; ring
  have hpos : 0 < g * (8 * A + B) := by omega
  have h8 : 0 < 8 * A + B := pos_of_mul_pos_right hpos (by omega)
  have hA0 : 0 ≤ A := nonneg_of_mul_nonneg_right (hA ▸ hdx0) (by omega)
  have hlt : 8 * A + B < g * (8 * A + B) := by
    have := mul_le_mul_of_nonneg_right hg2 h8.le
    linarith
  have hy1 : ((j % 8 : ℕ) : ℤ) < 8 := by omega
  have hy2 : ((i % 8 : ℕ) : ℤ) < 8 := by omega
  have hyb : 0 ≤ ((i % 8 : ℕ) : ℤ) + B ∧ ((i % 8 : ℕ) : ℤ) + B < 8 := by
    rcases le_or_gt 0 B with hB0 | hB0
    · have := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ g by omega) hB0
      constructor
      · omega
      · linarith
    · have := mul_le_mul_of_nonpos_right (show (1 : ℤ) ≤ g by omega) hB0.le
      constructor
      · linarith
      · omega
  set k : ℕ := ((i : ℤ) + 8 * A + B).toNat with hk
  apply H k (by omega) (by omega)
  simp only [Collinear3, pt]
  have hk1 : ((k / 8 : ℕ) : ℤ) = ((i / 8 : ℕ) : ℤ) + A := by omega
  have hk2 : ((k % 8 : ℕ) : ℤ) = ((i % 8 : ℕ) : ℤ) + B := by omega
  rw [hk1, hk2, ← hdx, ← hdy, hA, hB]
  ring

theorem back_of_isFirst {i j : ℕ} (hij : i < j) (H : IsFirst i j) :
    ¬(j / 8 ≤ 2 * (i / 8) ∧ j % 8 ≤ 2 * (i % 8) ∧ 2 * (i % 8) < 8 + j % 8) := by
  rintro ⟨h1, h2, h3⟩
  apply H (2 * i - j) (by omega) (by omega)
  simp only [Collinear3, pt]
  have hk1 : (((2 * i - j) / 8 : ℕ) : ℤ) = 2 * ((i / 8 : ℕ) : ℤ) - ((j / 8 : ℕ) : ℤ) := by
    omega
  have hk2 : (((2 * i - j) % 8 : ℕ) : ℤ) = 2 * ((i % 8 : ℕ) : ℤ) - ((j % 8 : ℕ) : ℤ) := by
    omega
  rw [hk1, hk2]
  ring

theorem isFirst_of {i j : ℕ} (hij : i < j)
    (hg : Int.gcd (((j / 8 : ℕ) : ℤ) - ((i / 8 : ℕ) : ℤ))
      (((j % 8 : ℕ) : ℤ) - ((i % 8 : ℕ) : ℤ)) = 1)
    (hback : ¬(j / 8 ≤ 2 * (i / 8) ∧ j % 8 ≤ 2 * (i % 8) ∧ 2 * (i % 8) < 8 + j % 8)) :
    IsFirst i j := by
  intro k hkj hki hcol
  simp only [Collinear3, pt] at hcol
  have hji : (j : ℤ) - i = 8 * (((j / 8 : ℕ) : ℤ) - ((i / 8 : ℕ) : ℤ)) +
      (((j % 8 : ℕ) : ℤ) - ((i % 8 : ℕ) : ℤ)) := by omega
  have hki0 : (k : ℤ) - i = 8 * (((k / 8 : ℕ) : ℤ) - ((i / 8 : ℕ) : ℤ)) +
      (((k % 8 : ℕ) : ℤ) - ((i % 8 : ℕ) : ℤ)) := by omega
  have hxk : (0 : ℤ) ≤ ((k / 8 : ℕ) : ℤ) := by positivity
  have hyk0 : (0 : ℤ) ≤ ((k % 8 : ℕ) : ℤ) := by positivity
  have hyk : ((k % 8 : ℕ) : ℤ) < 8 := by omega
  have hyi : ((i % 8 : ℕ) : ℤ) < 8 := by omega
  have hxij : i / 8 ≤ j / 8 := Nat.div_le_div_right hij.le
  set dx : ℤ := ((j / 8 : ℕ) : ℤ) - ((i / 8 : ℕ) : ℤ) with hdx
  set dy : ℤ := ((j % 8 : ℕ) : ℤ) - ((i % 8 : ℕ) : ℤ) with hdy
  set ex : ℤ := ((k / 8 : ℕ) : ℤ) - ((i / 8 : ℕ) : ℤ) with hex
  set ey : ℤ := ((k % 8 : ℕ) : ℤ) - ((i % 8 : ℕ) : ℤ) with hey
  have hb := Int.gcd_eq_gcd_ab dx dy
  rw [hg, Nat.cast_one] at hb
  set u := Int.gcdA dx dy
  set v := Int.gcdB dx dy
  set t := ex * u + ey * v with ht
  have htx : ex = t * dx := by linear_combination ex * hb - v * hcol
  have hty : ey = t * dy := by linear_combination ey * hb + u * hcol
  have hki' : (k : ℤ) - i = t * ((j : ℤ) - i) := by
    rw [hji, hki0, htx, hty]
    ring
  have hpos : (0 : ℤ) < j - i := by omega
  have ht1 : t < 1 := by
    by_contra h
    push Not at h
    have := mul_le_mul_of_nonneg_right h hpos.le
    have : (k : ℤ) - i ≥ (j : ℤ) - i := by rw [hki']; linarith
    omega
  have ht0 : t ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hki'
    omega
  have htm : t ≤ -1 := by omega
  have hdx0 : 0 ≤ dx := by omega
  apply hback
  have hc1 : dx ≤ ((i / 8 : ℕ) : ℤ) := by
    have := mul_le_mul_of_nonneg_right htm hdx0
    linarith
  have hc2 : dy ≤ ((i % 8 : ℕ) : ℤ) ∧ ((i % 8 : ℕ) : ℤ) - dy < 8 := by
    rcases le_or_gt 0 dy with h0 | h0
    · have := mul_le_mul_of_nonneg_right htm h0
      constructor
      · linarith
      · omega
    · have := mul_le_mul_of_nonpos_right htm h0.le
      constructor
      · omega
      · linarith
  omega

/-- For `i < j`, `pt i` and `pt j` are the two smallest grid points of their line iff
`goodF i j`. -/
theorem isFirst_iff {i j : ℕ} (hij : i < j) :
    IsFirst i j ↔ goodF i j = true := by
  have hxij : i / 8 ≤ j / 8 := Nat.div_le_div_right hij.le
  rw [goodF_iff, gcd_eq i j hxij]
  exact ⟨fun H => ⟨gcd_of_isFirst hij H, back_of_isFirst hij H⟩,
    fun ⟨hg, hb⟩ => isFirst_of hij hg hb⟩

/-- `countI j m` is the number of `i < m` with `goodF i j` (`countI_eq`). -/
def countI (j m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i r => cond (goodF i j) (r + 1) r) m

/-- `countJ m = ∑_{j < m} countI j j` (`countJ_eq`). -/
def countJ (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j r => r + countI j j) m

/-- Fast evaluation of `a` (`a_eq_aFast`). -/
def aFast (n : ℕ) : ℕ := countJ (8 * n)

theorem countI_eq (j m : ℕ) :
    countI j m = ((Finset.range m).filter fun i => goodF i j = true).card := by
  induction m with
  | zero => simp [countI]
  | succ m ih =>
    show cond (goodF m j) (countI j m + 1) (countI j m) = _
    rw [Finset.range_add_one, Finset.filter_insert, ih]
    cases h : goodF m j
    · simp
    · simp

theorem countJ_eq (m : ℕ) : countJ m = ∑ j ∈ Finset.range m, countI j j := by
  induction m with
  | zero => simp [countJ]
  | succ m ih =>
    show countJ m + countI m m = _
    rw [Finset.sum_range_succ, ih]

theorem a_eq_aFast (n : ℕ) : a n = aFast n := by
  rw [a_eq_card_firstPairs, firstPairs, Finset.card_sigma, aFast, countJ_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [countI_eq]
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  exact isFirst_iff (Finset.mem_range.mp hi)

/-! ### Data -/

set_option maxRecDepth 100000 in
/-- The definition reproduces the 41 terms `a(0), …, a(40)` listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 41).map a =
    [0, 1, 66, 131, 238, 361, 534, 709, 938, 1183, 1470, 1759, 2104, 2459, 2870, 3287, 3740, 4209,
      4734, 5261, 5844, 6437, 7070, 7711, 8408, 9115, 9872, 10637, 11444, 12265, 13142, 14015,
      14944, 15889, 16876, 17871, 18914, 19967, 21076, 22193, 23352] := by
  rw [show a = aFast from funext a_eq_aFast]
  decide +kernel

/-- The listed terms `a(0), …, a(40)`. -/
def listed : List ℕ :=
  [0, 1, 66, 131, 238, 361, 534, 709, 938, 1183, 1470, 1759, 2104, 2459, 2870, 3287, 3740, 4209,
    4734, 5261, 5844, 6437, 7070, 7711, 8408, 9115, 9872, 10637, 11444, 12265, 13142, 14015,
    14944, 15889, 16876, 17871, 18914, 19967, 21076, 22193, 23352]

theorem a_eq_listed {n : ℕ} (hn : n < 41) : a n = listed.getD n 0 := by
  have := congrArg (fun l => l.getD n 0) a_data
  simpa [listed, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn] using this

/-! ### The conjecture -/

/-- Barker's recurrence at index `n` for a sequence `f`:
`f(n) = -f(n-2) + f(n-5) + f(n-6) + 2f(n-7) + f(n-8) + f(n-9) - f(n-11) - f(n-12) - 2f(n-13)
- f(n-14) - f(n-15) + f(n-18) + f(n-20)`. -/
def Recurrence (f : ℕ → ℤ) (n : ℕ) : Prop :=
  f n = -f (n - 2) + f (n - 5) + f (n - 6) + 2 * f (n - 7) + f (n - 8) + f (n - 9)
    - f (n - 11) - f (n - 12) - 2 * f (n - 13) - f (n - 14) - f (n - 15) + f (n - 18) + f (n - 20)

instance (f : ℕ → ℤ) (n : ℕ) : Decidable (Recurrence f n) :=
  inferInstanceAs (Decidable (_ = _))

/-- Sanity check (not a proof of the conjecture): the listed terms satisfy the recurrence for
`22 ≤ n ≤ 40`. -/
theorem recurrence_data (n : ℕ) (h1 : 21 < n) (h2 : n ≤ 40) :
    Recurrence (fun m => (a m : ℤ)) n := by
  have key : ∀ m < 41, 21 < m → Recurrence (fun m => (listed.getD m 0 : ℤ)) m := by
    decide +kernel
  unfold Recurrence at *
  simp (disch := omega) only [a_eq_listed]
  exact key n (by omega) h1

/-- Barker's conjecture (recurrence form): for all `n > 21`,
`a(n) = -a(n-2) + a(n-5) + a(n-6) + 2a(n-7) + a(n-8) + a(n-9) - a(n-11) - a(n-12) - 2a(n-13)
- a(n-14) - a(n-15) + a(n-18) + a(n-20)`. -/
def statement : Prop :=
  ∀ n : ℕ, 21 < n → Recurrence (fun m => (a m : ℤ)) n

open PowerSeries in
/-- Barker's conjecture (g.f. form), as an identity of formal power series over `ℤ`:
`(∑ a(n) xⁿ) · (1 - x)³(1 + x)(1 - x + x²)(1 + x²)(1 + x + x²)(1 + x + ⋯ + x⁴)(1 + x + ⋯ + x⁶)
= x(1 + 66x + ⋯ + 8x²⁰)`. -/
def statement_gf : Prop :=
  PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2) *
        (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6)) =
    X * (1 + 66 * X + 132 * X ^ 2 + 304 * X ^ 3 + 492 * X ^ 4 + 771 * X ^ 5 + 1003 * X ^ 6 +
      1273 * X ^ 7 + 1390 * X ^ 8 + 1480 * X ^ 9 + 1374 * X ^ 10 + 1241 * X ^ 11 + 971 * X ^ 12 +
      739 * X ^ 13 + 476 * X ^ 14 + 296 * X ^ 15 + 140 * X ^ 16 + 74 * X ^ 17 + 17 * X ^ 18 +
      8 * X ^ 19 + 8 * X ^ 20)

end Math0.Statements.A160848
