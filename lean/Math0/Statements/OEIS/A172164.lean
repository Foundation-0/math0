/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A172164: second differences of the turns of the spiral of Theodorus

Source: https://oeis.org/A172164, Sébastien Dumortier, Jan 27 2010 (COMMENTS section).
Verbatim:
> Conjecture : The terms are only 18,19,20,21 (From the first thousand turns, there are 2,3% of
> 18, 36,5% of 19, 46,2% of 20 and 15% of 21). No period found. Probably due to Pi transcendence.

The entry's name: "Differences between numbers of triangles entirely contained in two consecutive
turns of Pythagoras's snail (Theodorus spiral)." Offset `2`; data `20, 19, 20, 19, 20, 21, 18, 21,
19, 20, …` (69 terms). Example: "In the first turn, 16 triangles are complete. In the 2nd turn,
there are 36 triangles completely included. The difference is 20."

## Encoding

* *The spiral.* Pythagoras's snail (A137515) starts with the isosceles right triangle with legs
  `1, 1`; each next right triangle has as legs the previous hypotenuse and a side of length `1`.
  So triangle `i` (`i ≥ 1`) has legs `√i`, `1` and hypotenuse `√(i+1)`, and its angle at the
  centre is `arctan (1 / √i)`. The triangles are laid side by side around the centre, starting
  from a fixed ray (the first leg of length `1`), so triangle `i` occupies the angular sector
  `[S (i-1), S i]`, where `S k = ∑_{i=1}^{k} arctan (1 / √i)` is the total angle of the first
  `k` triangles (`S 0 = 0`). This is the formula of A072895 ("least k such that
  Sum_{i=1..k} arctan(1/sqrt(i)) > 2n*Pi").
* *Turns.* The `n`-th turn (`n ≥ 1`) is the range of angles `[2π(n-1), 2πn]`. Triangle `i` is
  *entirely contained* in turn `n` iff `2π(n-1) ≤ S (i-1)` and `S i ≤ 2πn`
  (`turnTriangles n`). The bounds are taken closed; the strict and non-strict versions agree on
  every turn checked below, since there `S` never hits a multiple of `2π`.
* `c n = (turnTriangles n).ncard` is the number of triangles entirely contained in turn `n`.
  The set is finite for every `n` (`turnTriangles_finite`, from `S k ≥ (5/6) √k`), so `c n` is
  a true count.
* The sequence: `a n = c n - c (n - 1)` for `n ≥ 2` (offset `2`), computed in `ℤ` (the
  difference of two counts, so that no truncated subtraction is involved). `a 0`, `a 1` are not
  terms of the sequence.
* *The conjecture* (`statement`): for every `n ≥ 2`, `a n ∈ {18, 19, 20, 21}`. The percentages
  and the remarks "No period found. Probably due to Pi transcendence." are observations, not part
  of the formalized claim.

## Data check

`a` is not computable (it is defined through real numbers), so the data are proved as follows.
Write `K n` for the number of triangles in the first `n` turns, i.e. the largest `k` with
`S k ≤ 2πn` (this is A137515; `Kseq` lists `K 1, …, K 70`, and its first 42 entries are the 42
listed terms of A137515, `Kseq_A137515`). The theorem `crossing` proves
`S (K n) < 2πn < S (K n + 1)` for `n = 1, …, 70`. From this, `turnTriangles 1 = [1, K 1]` and
`turnTriangles n = [K (n-1) + 2, K n]` for `n ≥ 2` (triangle `K (n-1) + 1` straddles the ray at
angle `2π(n-1)`). Hence `c 1 = K 1 = 16`, `c n = K n - K (n-1) - 1`, `c 2 = 36` (the entry's
example), and `a_data` checks all 69 listed terms `a 2, …, a 70` against the real definition.
(Equivalently `a n = L n - 2 L (n-1) + L (n-2)` with `L n = K n + 1` = A072895(n) and `L 0 = 0`,
the entry's formula "The second forward difference of A072895".)

`crossing` is a rigorous, kernel-checked interval computation (`check_targets`, about half a minute
of kernel time). With `S (k+1) = π/4 + R k`, where `R k = ∑_{j=2}^{k+1} arctan (1/√j)`, each term
is enclosed using the alternating Maclaurin series of `arctan` (`Real.hasSum_arctan`, with
partial sums bracketing the limit, `arctan_alt_bounds`): for `x = 1/√j`,
`arctan x = x ∑ (-1)^m j^(-m) / (2m+1)`. `x` is enclosed by integers `qlo/2^50 ≤ x ≤ qhi/2^50`
(checked by `qlo² j ≤ 2^100 ≤ qhi² j`), and every series term is rounded down or up to an
integer multiple of `2^-50` (`term_lower`, `term_upper`). The sums run through
`j ≤ K 70 + 1 = 48836`, and they are compared with `2πn - π/4` using
`3.14159265358979323846 < π < 3.14159265358979323847` (`Real.pi_gt_d20`, `Real.pi_lt_d20`).
The accumulated width of the enclosure is about `10⁻⁷`; the smallest gap between `2πn` and the
`S k` for `n ≤ 70` is about `2·10⁻⁵` (at `n = 53`). Soundness of the computation
(`walkK_spec`, `checkK_sound`) is proved for every input, so the kernel only evaluates
arithmetic.
-/

namespace Math0.Statements.A172164

open Real Finset Filter Topology

/-! ### The definitions -/

/-- `S k = ∑_{i=1}^{k} arctan (1 / √i)`: the total angle at the centre of the first `k`
triangles of the spiral of Theodorus (triangle `i` has legs `√i` and `1`). -/
noncomputable def S (k : ℕ) : ℝ := ∑ i ∈ range k, arctan (1 / √((i : ℝ) + 1))

/-- The triangles entirely contained in the `n`-th turn: triangle `i ≥ 1` occupies the angular
sector `[S (i-1), S i]`, and the `n`-th turn is `[2π(n-1), 2πn]`. -/
def turnTriangles (n : ℕ) : Set ℕ :=
  {i | 1 ≤ i ∧ 2 * π * ((n : ℝ) - 1) ≤ S (i - 1) ∧ S i ≤ 2 * π * n}

/-- The number of triangles entirely contained in the `n`-th turn of Pythagoras's snail. -/
noncomputable def c (n : ℕ) : ℕ := (turnTriangles n).ncard

/-- A172164 (offset `2`): the difference between the numbers of triangles entirely contained in
the turns `n` and `n - 1`. -/
noncomputable def a (n : ℕ) : ℤ := (c n : ℤ) - c (n - 1)

/-! ### Bounds on `arctan` from its alternating Maclaurin series -/

/-- For `0 ≤ x < 1`, the partial sums of `∑ (-1)^i x^(2i+1)/(2i+1)` with an even (resp. odd)
number of terms are lower (resp. upper) bounds for `arctan x`. -/
theorem arctan_alt_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ≤ arctan x ∧
    arctan x ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  have ht : Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)))
      atTop (𝓝 (arctan x)) := by
    have := hs.tendsto_sum_nat
    simpa only [mul_div_assoc] using this
  have hf : Antitone (fun i : ℕ => x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) := by
    refine antitone_nat_of_succ_le fun i => ?_
    have h1 : x ^ (2 * (i + 1) + 1) ≤ x ^ (2 * i + 1) :=
      pow_le_pow_of_le_one hx0 hx1.le (by omega)
    have h2 : ((2 * i + 1 : ℕ) : ℝ) ≤ ((2 * (i + 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 * i + 1 ≤ 2 * (i + 1) + 1)
    have h3 : (0 : ℝ) < ((2 * i + 1 : ℕ) : ℝ) := by positivity
    exact div_le_div₀ (by positivity) h1 h3 h2
  exact ⟨hf.alternating_series_le_tendsto ht k, hf.tendsto_le_alternating_series ht k⟩

/-- `serA j r = ∑_{i<r} j^(-2i) / (4i+1)`. -/
noncomputable def serA (j : ℝ) (r : ℕ) : ℝ := ∑ i ∈ range r, j⁻¹ ^ (2 * i) / (4 * i + 1)

/-- `serB j r = ∑_{i<r} j^(-(2i+1)) / (4i+3)`. -/
noncomputable def serB (j : ℝ) (r : ℕ) : ℝ := ∑ i ∈ range r, j⁻¹ ^ (2 * i + 1) / (4 * i + 3)

theorem serA_succ (j : ℝ) (r : ℕ) : serA j (r + 1) = serA j r + j⁻¹ ^ (2 * r) / (4 * r + 1) := by
  rw [serA, serA, sum_range_succ]

theorem serB_succ (j : ℝ) (r : ℕ) :
    serB j (r + 1) = serB j r + j⁻¹ ^ (2 * r + 1) / (4 * r + 3) := by
  rw [serB, serB, sum_range_succ]

theorem alt_sum_even {x j : ℝ} (hx : x ^ 2 = j⁻¹) (r : ℕ) :
    ∑ i ∈ range (2 * r), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) =
      x * (serA j r - serB j r) := by
  induction r with
  | zero => simp [serA, serB]
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, serA_succ,
      serB_succ]
    have e1 : x ^ (2 * (2 * r) + 1) = x * j⁻¹ ^ (2 * r) := by
      rw [pow_succ, pow_mul, hx]; ring
    have e2 : x ^ (2 * (2 * r + 1) + 1) = x * j⁻¹ ^ (2 * r + 1) := by
      rw [pow_succ, pow_mul, hx]; ring
    have c1 : ((2 * (2 * r) + 1 : ℕ) : ℝ) = 4 * r + 1 := by push_cast; ring
    have c2 : ((2 * (2 * r + 1) + 1 : ℕ) : ℝ) = 4 * r + 3 := by push_cast; ring
    have s1 : (-1 : ℝ) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
    have s2 : (-1 : ℝ) ^ (2 * r + 1) = -1 := by rw [pow_succ, s1]; norm_num
    rw [e1, e2, c1, c2, s1, s2]
    ring

theorem alt_sum_odd {x j : ℝ} (hx : x ^ 2 = j⁻¹) (r : ℕ) :
    ∑ i ∈ range (2 * r + 1), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) =
      x * (serA j (r + 1) - serB j r) := by
  rw [sum_range_succ, alt_sum_even hx r, serA_succ]
  have e1 : x ^ (2 * (2 * r) + 1) = x * j⁻¹ ^ (2 * r) := by
    rw [pow_succ, pow_mul, hx]; ring
  have c1 : ((2 * (2 * r) + 1 : ℕ) : ℝ) = 4 * r + 1 := by push_cast; ring
  have s1 : (-1 : ℝ) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
  rw [e1, c1, s1]
  ring

theorem serA_sub_serB_nonneg {j : ℝ} (hj : 1 ≤ j) (r : ℕ) : 0 ≤ serA j r - serB j r := by
  rw [serA, serB, ← sum_sub_distrib]
  refine sum_nonneg fun i _ => ?_
  rw [sub_nonneg]
  have hj0 : 0 < j⁻¹ := by positivity
  have hj1 : j⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj
  have h1 : j⁻¹ ^ (2 * i + 1) ≤ j⁻¹ ^ (2 * i) := pow_le_pow_of_le_one hj0.le hj1 (by omega)
  have h2 : (4 * (i : ℝ) + 1) ≤ 4 * i + 3 := by linarith
  exact div_le_div₀ (by positivity) h1 (by positivity) h2

theorem serA_le_serA_succ {j : ℝ} (hj : 0 < j) (r : ℕ) : serA j r ≤ serA j (r + 1) := by
  rw [serA_succ]
  have : 0 ≤ j⁻¹ ^ (2 * r) / (4 * r + 1) := by positivity
  linarith

/-! ### Rounding to integers -/

/-- `sumPos q j r = ∑_{i<r} ⌊q / ((4i+1) j^(2i))⌋` (written with the recursor and primitive
operations, for kernel evaluation). -/
def sumPos (q j : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => Nat.add ih
      (Nat.div q (Nat.mul (Nat.add (Nat.mul 4 i) 1) (Nat.pow j (Nat.mul 2 i)))))

/-- `sumNeg q j r = ∑_{i<r} ⌊q / ((4i+3) j^(2i+1))⌋`. -/
def sumNeg (q j : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => Nat.add ih
      (Nat.div q (Nat.mul (Nat.add (Nat.mul 4 i) 3) (Nat.pow j (Nat.add (Nat.mul 2 i) 1)))))

theorem sumPos_succ (q j r : ℕ) :
    sumPos q j (r + 1) = sumPos q j r + q / ((4 * r + 1) * j ^ (2 * r)) := rfl

theorem sumNeg_succ (q j r : ℕ) :
    sumNeg q j (r + 1) = sumNeg q j r + q / ((4 * r + 3) * j ^ (2 * r + 1)) := rfl

theorem cast_div_le_add_one (m n : ℕ) (hn : 0 < n) : (m : ℝ) / n ≤ ((m / n : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_mul_div_succ m hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  have : (m : ℝ) < n * (((m / n : ℕ) : ℝ) + 1) := by exact_mod_cast h
  linarith

theorem sumPos_bounds (q j r : ℕ) (hj : 0 < j) :
    (sumPos q j r : ℝ) ≤ q * serA j r ∧ (q : ℝ) * serA j r ≤ sumPos q j r + r := by
  induction r with
  | zero => simp [sumPos, serA]
  | succ r ih =>
    rw [sumPos_succ, serA_succ]
    set N := (4 * r + 1) * j ^ (2 * r) with hN
    have hN0 : 0 < N := by positivity
    have hj0 : (j : ℝ) ≠ 0 := by positivity
    have e : (q : ℝ) * ((j : ℝ)⁻¹ ^ (2 * r) / (4 * r + 1)) = (q : ℝ) / (N : ℝ) := by
      rw [hN, inv_pow]; push_cast; field_simp
    have h1 : ((q / N : ℕ) : ℝ) ≤ (q : ℝ) / N := Nat.cast_div_le
    have h2 := cast_div_le_add_one q N hN0
    rw [Nat.cast_add, mul_add, e, Nat.cast_succ]
    constructor
    · linarith [ih.1]
    · linarith [ih.2]

theorem sumNeg_bounds (q j r : ℕ) (hj : 0 < j) :
    (sumNeg q j r : ℝ) ≤ q * serB j r ∧ (q : ℝ) * serB j r ≤ sumNeg q j r + r := by
  induction r with
  | zero => simp [sumNeg, serB]
  | succ r ih =>
    rw [sumNeg_succ, serB_succ]
    set N := (4 * r + 3) * j ^ (2 * r + 1) with hN
    have hN0 : 0 < N := by positivity
    have hj0 : (j : ℝ) ≠ 0 := by positivity
    have e : (q : ℝ) * ((j : ℝ)⁻¹ ^ (2 * r + 1) / (4 * r + 3)) = (q : ℝ) / (N : ℝ) := by
      rw [hN, inv_pow]; push_cast; field_simp
    have h1 : ((q / N : ℕ) : ℝ) ≤ (q : ℝ) / N := Nat.cast_div_le
    have h2 := cast_div_le_add_one q N hN0
    rw [Nat.cast_add, mul_add, e, Nat.cast_succ]
    constructor
    · linarith [ih.1]
    · linarith [ih.2]

/-! ### Enclosing one term `arctan (1 / √j)` -/

/-- The scale `2^50` of the fixed-point computation. -/
def scale : ℕ := 1125899906842624

theorem scale_eq : scale = 2 ^ 50 := by norm_num [scale]

/-- `scale2 = scale * scale = 2^100`. -/
def scale2 : ℕ := 1267650600228229401496703205376

theorem scale2_eq : scale2 = scale * scale := by norm_num [scale2, scale]

theorem inv_sqrt_facts (j : ℕ) (hj : 2 ≤ j) :
    0 ≤ 1 / √(j : ℝ) ∧ 1 / √(j : ℝ) < 1 ∧ (1 / √(j : ℝ)) ^ 2 = (j : ℝ)⁻¹ := by
  have hj0 : (0 : ℝ) < j := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_lt_one (Real.sqrt_pos.2 hj0), Real.lt_sqrt (by norm_num)]
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  · rw [div_pow, Real.sq_sqrt hj0.le, one_pow, one_div]

/-- Lower bound: if `ql² j ≤ scale²` then
`sumPos ql j r - sumNeg ql j r - r ≤ scale · arctan (1/√j)`. -/
theorem term_lower (j : ℕ) (hj : 2 ≤ j) (r ql : ℕ) (hql : ql * ql * j ≤ scale * scale) :
    (sumPos ql j r : ℝ) - (sumNeg ql j r + r) ≤ scale * arctan (1 / √(j : ℝ)) := by
  obtain ⟨hx0, hx1, hx2⟩ := inv_sqrt_facts j hj
  set x := 1 / √(j : ℝ) with hx
  have hj0 : (0 : ℝ) < j := by positivity
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have hD : (0 : ℝ) ≤ scale := by positivity
  have hlo : (ql : ℝ) ≤ scale * x := by
    have h : (ql : ℝ) * ql * j ≤ scale * scale := by exact_mod_cast hql
    have hsq : (ql : ℝ) ^ 2 ≤ (scale * x) ^ 2 := by
      rw [mul_pow, hx2, le_mul_inv_iff₀ hj0]
      nlinarith [h]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  have hl := (arctan_alt_bounds hx0 hx1 r).1
  rw [alt_sum_even hx2] at hl
  have hAB := serA_sub_serB_nonneg hj1 r
  obtain ⟨p1, -⟩ := sumPos_bounds ql j r (by omega)
  obtain ⟨-, n2⟩ := sumNeg_bounds ql j r (by omega)
  have k1 : (ql : ℝ) * (serA j r - serB j r) ≤ scale * x * (serA j r - serB j r) :=
    mul_le_mul_of_nonneg_right hlo hAB
  have k2 : (scale : ℝ) * (x * (serA j r - serB j r)) ≤ scale * arctan x :=
    mul_le_mul_of_nonneg_left hl hD
  nlinarith [k1, k2, p1, n2]

/-- Upper bound: if `scale² ≤ qh² j` then
`scale · arctan (1/√j) ≤ sumPos qh j (r+1) + (r+1) - sumNeg qh j r`. -/
theorem term_upper (j : ℕ) (hj : 2 ≤ j) (r qh : ℕ) (hqh : scale * scale ≤ qh * qh * j) :
    scale * arctan (1 / √(j : ℝ)) ≤ (sumPos qh j (r + 1) : ℝ) + ((r : ℝ) + 1) - sumNeg qh j r := by
  obtain ⟨hx0, hx1, hx2⟩ := inv_sqrt_facts j hj
  set x := 1 / √(j : ℝ) with hx
  have hj0 : (0 : ℝ) < j := by positivity
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have hD : (0 : ℝ) ≤ scale := by positivity
  have hhi : (scale : ℝ) * x ≤ qh := by
    have h : (scale : ℝ) * scale ≤ qh * qh * j := by exact_mod_cast hqh
    have hsq : (scale * x) ^ 2 ≤ (qh : ℝ) ^ 2 := by
      rw [mul_pow, hx2, mul_inv_le_iff₀ hj0]
      nlinarith [h]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  have hu := (arctan_alt_bounds hx0 hx1 r).2
  rw [alt_sum_odd hx2] at hu
  have hAB : 0 ≤ serA j (r + 1) - serB j r := by
    have := serA_sub_serB_nonneg hj1 r
    have := serA_le_serA_succ hj0 r
    linarith
  obtain ⟨-, p2⟩ := sumPos_bounds qh j (r + 1) (by omega)
  obtain ⟨n1, -⟩ := sumNeg_bounds qh j r (by omega)
  have k1 : (scale : ℝ) * x * (serA j (r + 1) - serB j r) ≤ qh * (serA j (r + 1) - serB j r) :=
    mul_le_mul_of_nonneg_right hhi hAB
  have k2 : (scale : ℝ) * arctan x ≤ scale * (x * (serA j (r + 1) - serB j r)) :=
    mul_le_mul_of_nonneg_left hu hD
  push_cast at p2
  nlinarith [k1, k2, p2, n1]

/-! ### The angle sums -/

/-- `R k = ∑_{j=2}^{k+1} arctan (1 / √j)`, so that `S (k + 1) = π/4 + R k`. -/
noncomputable def R (k : ℕ) : ℝ := ∑ i ∈ range k, arctan (1 / √(((i + 2 : ℕ) : ℝ)))

theorem R_succ (k : ℕ) : R (k + 1) = R k + arctan (1 / √(((k + 2 : ℕ) : ℝ))) := by
  rw [R, R, sum_range_succ]

theorem S_succ_eq_R (k : ℕ) : S (k + 1) = π / 4 + R k := by
  rw [S, sum_range_succ', R, add_comm]
  congr 1
  · simp
  · refine sum_congr rfl fun i _ => ?_
    congr 3
    push_cast
    ring

theorem S_succ (k : ℕ) : S (k + 1) = S k + arctan (1 / √((k : ℝ) + 1)) := by
  rw [S, S, sum_range_succ]

theorem S_strictMono : StrictMono S := strictMono_nat_of_lt_succ fun k => by
  rw [S_succ]
  have : 0 < arctan (1 / √((k : ℝ) + 1)) := arctan_pos.2 (by positivity)
  linarith

theorem S_zero : S 0 = 0 := by simp [S]

theorem S_nonneg (k : ℕ) : 0 ≤ S k := S_zero ▸ S_strictMono.monotone (Nat.zero_le k)

/-! ### Kernel-friendly evaluation -/

/-- `x && y`, written with the recursor. -/
def andK (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false y x

theorem lt_of_blt {x y : ℕ} (h : Nat.blt x y = true) : x < y := by
  simpa [Nat.blt_eq] using h

theorem andK_eq_true (x y : Bool) : andK x y = true ↔ x = true ∧ y = true := by
  cases x <;> cases y <;> decide

/-- Newton's iteration for `⌊√n⌋` started at `x`, stopping once it no longer decreases, with at
most `fuel` steps. (Only its speed matters: `qloOf` and `qhiOf` check their results.) -/
def isqrtK (n : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun x => x)
    (fun _ ih x => Bool.rec (motive := fun _ => ℕ) (ih (Nat.div (Nat.add x (Nat.div n x)) 2)) x
      (Nat.ble x (Nat.div (Nat.add x (Nat.div n x)) 2)))

/-- `s` if `s² j ≤ scale²` (so `s / scale ≤ 1/√j`), else `0`. -/
def qloOf (j s : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0 s (Nat.ble (Nat.mul (Nat.mul s s) j) scale2)

/-- `s + 1` if `scale² ≤ (s+1)² j` (so `1/√j ≤ (s+1) / scale`), else `scale`. -/
def qhiOf (j s : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) scale (Nat.succ s)
    (Nat.ble scale2 (Nat.mul (Nat.mul (Nat.succ s) (Nat.succ s)) j))

theorem qloOf_spec (j s : ℕ) : qloOf j s * qloOf j s * j ≤ scale * scale := by
  unfold qloOf
  cases h : Nat.ble (Nat.mul (Nat.mul s s) j) scale2 with
  | false => show 0 * 0 * j ≤ scale * scale; simp
  | true =>
    show s * s * j ≤ scale * scale
    rw [← scale2_eq]
    exact Nat.le_of_ble_eq_true h

theorem qhiOf_spec (j s : ℕ) (hj : 1 ≤ j) : scale * scale ≤ qhiOf j s * qhiOf j s * j := by
  unfold qhiOf
  cases h : Nat.ble scale2 (Nat.mul (Nat.mul (Nat.succ s) (Nat.succ s)) j) with
  | false => show scale * scale ≤ scale * scale * j; exact Nat.le_mul_of_pos_right _ hj
  | true =>
    show scale * scale ≤ (s + 1) * (s + 1) * j
    rw [← scale2_eq]
    exact Nat.le_of_ble_eq_true h

/-- Number of series terms: starting from `r` and `p`, add `1` to `r` and multiply `p` by `j⁴`
until `e ≤ p` (at most `fuel` times). -/
def cntK (j e : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun r _ => r)
    (fun _ ih r p => Bool.rec (motive := fun _ => ℕ) (ih (Nat.succ r) (Nat.mul p (Nat.pow j 4))) r
      (Nat.ble e p))

/-- `2^66`. -/
def e66 : ℕ := 73786976294838206464

/-- Number of pairs of series terms used for the lower bound at `j` (`j^(4r+1) ≥ 2^66`). -/
def rl (j : ℕ) : ℕ := cntK j e66 40 1 (Nat.pow j 5)

/-- Number of pairs of series terms used for the upper bound at `j` (`j^(4r+3) ≥ 2^66`). -/
def ru (j : ℕ) : ℕ := cntK j e66 40 0 (Nat.pow j 3)

/-- One step of `walkK`: add the bounds for the term `j`, computed from `s ≈ scale/√j`, to the
running sums, and continue with `k`. -/
def stepK (j s a b c d : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) :
    ℕ × ℕ × ℕ × ℕ × ℕ :=
  k (Nat.succ j) s (Nat.add a (sumPos (qloOf j s) j (rl j)))
    (Nat.add b (Nat.add (sumNeg (qloOf j s) j (rl j)) (rl j)))
    (Nat.add c (Nat.add (sumPos (qhiOf j s) j (Nat.succ (ru j))) (Nat.succ (ru j))))
    (Nat.add d (sumNeg (qhiOf j s) j (ru j)))

/-- `walkK len j g a b c d` processes the terms `j, j+1, …, j+len-1`, starting from the
square-root guess `g` and the running sums `a, b, c, d`; it returns the last guess and the
four sums. -/
def walkK : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ × ℕ)
    (fun _ g a b c d => (g, a, b, c, d))
    (fun _ ih j g a b c d => stepK j (isqrtK (Nat.div scale2 j) 64 g) a b c d ih)

theorem walkK_zero (j g a b c d : ℕ) : walkK 0 j g a b c d = (g, a, b, c, d) := rfl

theorem walkK_succ (len j g a b c d : ℕ) : walkK (len + 1) j g a b c d =
    walkK len (j + 1) (isqrtK (scale2 / j) 64 g)
      (a + sumPos (qloOf j (isqrtK (scale2 / j) 64 g)) j (rl j))
      (b + (sumNeg (qloOf j (isqrtK (scale2 / j) 64 g)) j (rl j) + rl j))
      (c + (sumPos (qhiOf j (isqrtK (scale2 / j) 64 g)) j (ru j + 1) + (ru j + 1)))
      (d + sumNeg (qhiOf j (isqrtK (scale2 / j) 64 g)) j (ru j)) := rfl

/-- `Inv k a b c d`: the running sums enclose `scale · R k`. -/
def Inv (k a b c d : ℕ) : Prop := (a : ℝ) - b ≤ scale * R k ∧ scale * R k ≤ (c : ℝ) - d

theorem Inv_zero : Inv 0 0 0 0 0 := by simp [Inv, R]

theorem Inv_step (j s a b c d : ℕ) (hj : 2 ≤ j) (h : Inv (j - 2) a b c d) :
    Inv (j - 1) (a + sumPos (qloOf j s) j (rl j)) (b + (sumNeg (qloOf j s) j (rl j) + rl j))
      (c + (sumPos (qhiOf j s) j (ru j + 1) + (ru j + 1))) (d + sumNeg (qhiOf j s) j (ru j)) := by
  have hk : j - 1 = (j - 2) + 1 := by omega
  have hj2 : j - 2 + 2 = j := by omega
  rw [Inv, hk, R_succ, hj2]
  have hl := term_lower j hj (rl j) (qloOf j s) (qloOf_spec j s)
  have hu := term_upper j hj (ru j) (qhiOf j s) (qhiOf_spec j s (by omega))
  obtain ⟨h1, h2⟩ := h
  push_cast
  constructor <;> linarith

theorem walkK_spec (len : ℕ) : ∀ (j g a b c d : ℕ), 2 ≤ j → Inv (j - 2) a b c d →
    Inv (j - 2 + len) (walkK len j g a b c d).2.1 (walkK len j g a b c d).2.2.1
      (walkK len j g a b c d).2.2.2.1 (walkK len j g a b c d).2.2.2.2 := by
  induction len with
  | zero => intro j g a b c d _ h; simpa [walkK_zero] using h
  | succ len ih =>
    intro j g a b c d hj h
    rw [walkK_succ]
    have key := Inv_step j (isqrtK (scale2 / j) 64 g) a b c d hj h
    rw [show j - 1 = j + 1 - 2 by omega] at key
    have := ih (j + 1) (isqrtK (scale2 / j) 64 g) _ _ _ _ (by omega) key
    rwa [show j + 1 - 2 + len = j - 2 + (len + 1) by omega] at this

/-- The numerator of the lower bound `3.14159265358979323846` for `π`. -/
def piLo : ℕ := 314159265358979323846

/-- The numerator of the upper bound `3.14159265358979323847` for `π`. -/
def piHi : ℕ := 314159265358979323847

/-- `10^20`. -/
def e20 : ℕ := 100000000000000000000

theorem piLo_lt : (piLo : ℝ) / e20 < π := by
  have := Real.pi_gt_d20
  norm_num [piLo, e20] at this ⊢
  linarith

theorem pi_lt_piHi : π < (piHi : ℝ) / e20 := by
  have := Real.pi_lt_d20
  norm_num [piHi, e20] at this ⊢
  linarith

/-- `4 c 10^20 < piLo (8n - 1) scale + 4 d 10^20`: then `(c - d)/scale < π (8n-1)/4`. -/
def hiOK (n c d : ℕ) : Bool :=
  Nat.blt (Nat.mul (Nat.mul 4 c) e20)
    (Nat.add (Nat.mul (Nat.mul piLo (Nat.sub (Nat.mul 8 n) 1)) scale) (Nat.mul (Nat.mul 4 d) e20))

/-- `piHi (8n - 1) scale + 4 b 10^20 < 4 a 10^20`: then `π (8n-1)/4 < (a - b)/scale`. -/
def loOK (n a b : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul (Nat.mul piHi (Nat.sub (Nat.mul 8 n) 1)) scale)
    (Nat.mul (Nat.mul 4 b) e20)) (Nat.mul (Nat.mul 4 a) e20)

theorem S_lt_of_hiOK {n K c d : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K) (hinv : scale * R (K - 1) ≤ (c : ℝ) - d)
    (h : hiOK n c d = true) : S K < 2 * π * n := by
  have h' : 4 * c * e20 < piLo * (8 * n - 1) * scale + 4 * d * e20 := lt_of_blt h
  have h8 : ((8 * n - 1 : ℕ) : ℝ) = 8 * n - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hr : (4 : ℝ) * c * e20 < piLo * (8 * n - 1) * scale + 4 * d * e20 := by
    rw [← h8]; exact_mod_cast h'
  have hpi := piLo_lt
  have hn' : (0 : ℝ) < 8 * n - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hm : (piLo : ℝ) / e20 * (8 * n - 1) < π * (8 * n - 1) := mul_lt_mul_of_pos_right hpi hn'
  have hS : S K = π / 4 + R (K - 1) := by
    rw [← S_succ_eq_R, Nat.sub_add_cancel hK]
  rw [hS]
  have he : (0 : ℝ) < e20 := by norm_num [e20]
  have hs : (0 : ℝ) < scale := by norm_num [scale]
  rw [div_mul_eq_mul_div, div_lt_iff₀ he] at hm
  -- `4 e20 scale R ≤ 4 e20 (c - d) < piLo (8n-1) scale < π (8n-1) e20 scale`
  have k1 : (4 : ℝ) * e20 * (scale * R (K - 1)) ≤ 4 * e20 * ((c : ℝ) - d) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have k2 : (piLo : ℝ) * (8 * n - 1) * scale < π * (8 * n - 1) * e20 * scale :=
    mul_lt_mul_of_pos_right hm hs
  have k3 : (4 : ℝ) * R (K - 1) * (e20 * scale) < π * (8 * n - 1) * (e20 * scale) := by
    nlinarith [k1, k2, hr]
  have k4 : (4 : ℝ) * R (K - 1) < π * (8 * n - 1) := lt_of_mul_lt_mul_right k3 (by positivity)
  nlinarith [k4]

theorem lt_S_of_loOK {n K a b : ℕ} (hn : 1 ≤ n) (hinv : (a : ℝ) - b ≤ scale * R K)
    (h : loOK n a b = true) : 2 * π * n < S (K + 1) := by
  have h' : piHi * (8 * n - 1) * scale + 4 * b * e20 < 4 * a * e20 := lt_of_blt h
  have h8 : ((8 * n - 1 : ℕ) : ℝ) = 8 * n - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hr : (piHi : ℝ) * (8 * n - 1) * scale + 4 * b * e20 < 4 * a * e20 := by
    rw [← h8]; exact_mod_cast h'
  have hpi := pi_lt_piHi
  have hn' : (0 : ℝ) < 8 * n - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hm : π * (8 * n - 1) < (piHi : ℝ) / e20 * (8 * n - 1) := mul_lt_mul_of_pos_right hpi hn'
  rw [S_succ_eq_R]
  have he : (0 : ℝ) < e20 := by norm_num [e20]
  have hs : (0 : ℝ) < scale := by norm_num [scale]
  rw [div_mul_eq_mul_div, lt_div_iff₀ he] at hm
  have k1 : (4 : ℝ) * e20 * ((a : ℝ) - b) ≤ 4 * e20 * (scale * R K) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have k2 : π * (8 * n - 1) * e20 * scale < (piHi : ℝ) * (8 * n - 1) * scale :=
    mul_lt_mul_of_pos_right hm hs
  have k3 : π * (8 * n - 1) * (e20 * scale) < (4 : ℝ) * R K * (e20 * scale) := by
    nlinarith [k1, k2, hr]
  have k4 : π * (8 * n - 1) < (4 : ℝ) * R K := lt_of_mul_lt_mul_right k3 (by positivity)
  nlinarith [k4]

/-- Second half of a check step: the lower test at `K` (sums `w` enclose `scale · R K`), then the
rest of the list. -/
def check2 (n K : ℕ) (w : ℕ × ℕ × ℕ × ℕ × ℕ) (ih : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  andK (loOK n w.2.1 w.2.2.1) (ih K w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)

/-- First half of a check step: the upper test at `K - 1` (sums `w` enclose
`scale · R (K - 1)`), then one more term. -/
def check1 (n K : ℕ) (w : ℕ × ℕ × ℕ × ℕ × ℕ) (ih : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  andK (hiOK n w.2.2.2.1 w.2.2.2.2)
    (check2 n K (walkK 1 (Nat.succ K) w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2) ih)

/-- `checkK l cur g a b c d`: for each `(n, K)` in `l` (in increasing order of `K`), certify
`S K < 2πn < S (K + 1)`, given running sums `a, b, c, d` enclosing `scale · R cur`. -/
def checkK : List (ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (fun _ _ _ _ _ _ => true)
    (fun p _ ih cur g a b c d =>
      andK (Nat.blt cur p.2) (andK (Nat.ble 1 p.1)
        (check1 p.1 p.2 (walkK (Nat.sub (Nat.sub p.2 1) cur) (Nat.add cur 2) g a b c d) ih)))

theorem checkK_sound (l : List (ℕ × ℕ)) : ∀ (cur g a b c d : ℕ), Inv cur a b c d →
    checkK l cur g a b c d = true → ∀ p ∈ l, S p.2 < 2 * π * p.1 ∧ 2 * π * p.1 < S (p.2 + 1) := by
  induction l with
  | nil => intro _ _ _ _ _ _ _ _ p hp; simp at hp
  | cons q l ih =>
    intro cur g a b c d hinv h p hp
    obtain ⟨n, K⟩ := q
    have h0 : andK (Nat.blt cur K) (andK (Nat.ble 1 n)
        (check1 n K (walkK (K - 1 - cur) (cur + 2) g a b c d)
          (fun cur g a b c d => checkK l cur g a b c d))) = true := h
    simp only [andK_eq_true, check1, check2] at h0
    obtain ⟨hcur, hn, hhi, hlo, hrest⟩ := h0
    have hcur' : cur < K := lt_of_blt hcur
    have hn' : 1 ≤ n := Nat.le_of_ble_eq_true hn
    set w := walkK (K - 1 - cur) (cur + 2) g a b c d with hw
    have hw1 := walkK_spec (K - 1 - cur) (cur + 2) g a b c d (by omega)
      (by rwa [show cur + 2 - 2 = cur by omega])
    rw [← hw, show cur + 2 - 2 + (K - 1 - cur) = K - 1 by omega] at hw1
    set w' := walkK 1 (K + 1) w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 with hw'
    have hw2 := walkK_spec 1 (K + 1) w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 (by omega)
      (by rwa [show K + 1 - 2 = K - 1 by omega])
    rw [← hw', show K + 1 - 2 + 1 = K by omega] at hw2
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨S_lt_of_hiOK hn' (by omega) hw1.2 hhi, lt_S_of_loOK hn' hw2.1 hlo⟩
    · exact ih K w'.1 w'.2.1 w'.2.2.1 w'.2.2.2.1 w'.2.2.2.2 hw2 hrest p hp

/-! ### The turn boundaries `K n` for `n ≤ 70` -/

/-- `K 1, …, K 70`: `K n` is the number of triangles in the first `n` turns (A137515). -/
def Kseq : List ℕ :=
  [16, 53, 109, 185, 280, 395, 531, 685, 860, 1054, 1268, 1502, 1756, 2029, 2322, 2635, 2967,
    3319, 3691, 4083, 4494, 4926, 5376, 5847, 6337, 6848, 7377, 7927, 8496, 9086, 9694, 10323,
    10971, 11639, 12327, 13035, 13762, 14509, 15276, 16062, 16868, 17694, 18540, 19405, 20290,
    21195, 22120, 23064, 24029, 25012, 26016, 27039, 28082, 29145, 30228, 31330, 32452, 33594,
    34756, 35937, 37138, 38359, 39599, 40859, 42139, 43439, 44758, 46098, 47456, 48835]

/-- The first 42 entries of `Kseq` are the 42 listed terms of A137515. -/
theorem Kseq_A137515 : Kseq.take 42 = [16, 53, 109, 185, 280, 395, 531, 685, 860, 1054, 1268,
    1502, 1756, 2029, 2322, 2635, 2967, 3319, 3691, 4083, 4494, 4926, 5376, 5847, 6337, 6848, 7377,
    7927, 8496, 9086, 9694, 10323, 10971, 11639, 12327, 13035, 13762, 14509, 15276, 16062, 16868,
    17694] := by decide

/-- `K n` for `1 ≤ n ≤ 70`. -/
def Kof (n : ℕ) : ℕ := Kseq.getD (n - 1) 0

/-- The pairs `(n, K n)`, `n = 1, …, 70`. -/
def targets : List (ℕ × ℕ) := (List.range 70).map fun i => (i + 1, Kof (i + 1))

/-- The interval computation succeeds (kernel-checked). -/
theorem check_targets : checkK targets 0 scale 0 0 0 0 = true := by decide +kernel

/-- `S (K n) < 2πn < S (K n + 1)` for `n = 1, …, 70`. -/
theorem crossing (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 70) :
    S (Kof n) < 2 * π * n ∧ 2 * π * n < S (Kof n + 1) := by
  have hmem : (n, Kof n) ∈ targets := by
    refine List.mem_map.2 ⟨n - 1, List.mem_range.2 (by omega), ?_⟩
    rw [Nat.sub_add_cancel h1]
  exact checkK_sound targets 0 scale 0 0 0 0 Inv_zero check_targets (n, Kof n) hmem

/-! ### Counting the triangles of a turn -/

theorem S_le_iff {θ : ℝ} {K : ℕ} (h1 : S K < θ) (h2 : θ < S (K + 1)) (i : ℕ) :
    S i ≤ θ ↔ i ≤ K := by
  constructor
  · intro h
    by_contra hi
    have := S_strictMono.monotone (show K + 1 ≤ i by omega)
    linarith
  · intro hi
    have := S_strictMono.monotone hi
    linarith

theorem S_lt_iff {θ : ℝ} {K : ℕ} (h1 : S K < θ) (h2 : θ < S (K + 1)) (i : ℕ) :
    S i < θ ↔ i ≤ K := by
  constructor
  · intro h
    by_contra hi
    have := S_strictMono.monotone (show K + 1 ≤ i by omega)
    linarith
  · intro hi
    have := S_strictMono.monotone hi
    linarith

theorem turnTriangles_one {K : ℕ} (h1 : S K < 2 * π * (1 : ℕ)) (h2 : 2 * π * (1 : ℕ) < S (K + 1)) :
    turnTriangles 1 = Set.Icc 1 K := by
  ext i
  simp only [turnTriangles, Set.mem_ofPred_eq, Set.mem_Icc]
  rw [S_le_iff h1 h2]
  have := S_nonneg (i - 1)
  constructor
  · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨h, by push_cast; linarith, h'⟩

theorem turnTriangles_eq {n K K' : ℕ} (hn : 2 ≤ n)
    (h1 : S K < 2 * π * n) (h2 : 2 * π * n < S (K + 1))
    (h1' : S K' < 2 * π * (n - 1 : ℕ)) (h2' : 2 * π * (n - 1 : ℕ) < S (K' + 1)) :
    turnTriangles n = Set.Icc (K' + 2) K := by
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hc] at h1' h2'
  ext i
  have key : 2 * π * ((n : ℝ) - 1) ≤ S (i - 1) ↔ K' + 1 ≤ i - 1 := by
    rw [← not_lt, S_lt_iff h1' h2']
    omega
  simp only [turnTriangles, Set.mem_ofPred_eq, Set.mem_Icc]
  rw [key, S_le_iff h1 h2]
  omega

theorem ncard_Icc_nat (a b : ℕ) : (Set.Icc a b).ncard = b + 1 - a := by
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]

/-- The numbers of complete triangles in the turns `1, …, 70`, from `Kseq`. -/
def cK (n : ℕ) : ℕ := if n = 1 then Kof 1 else Kof n - Kof (n - 1) - 1

theorem c_eq (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 70) : c n = cK n := by
  obtain ⟨hA, hB⟩ := crossing n h1 h2
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · rw [c, turnTriangles_one hA hB, ncard_Icc_nat, cK, if_pos rfl]
    rfl
  · obtain ⟨hA', hB'⟩ := crossing (n - 1) (by omega) (by omega)
    rw [c, turnTriangles_eq hn hA hB hA' hB', ncard_Icc_nat, cK, if_neg (by omega)]
    omega

/-- The entry's example: 16 triangles are complete in the first turn and 36 in the second. -/
theorem c_one_two : c 1 = 16 ∧ c 2 = 36 := by
  rw [c_eq 1 le_rfl (by norm_num), c_eq 2 (by norm_num) (by norm_num)]
  decide

/-- The definition reproduces all 69 terms listed in OEIS, `a 2, …, a 70` (kernel-checked
interval computation `check_targets`). -/
theorem a_data : (List.range 69).map (fun i => a (i + 2)) =
    [20, 19, 20, 19, 20, 21, 18, 21, 19, 20, 20, 20, 19, 20, 20, 19, 20, 20, 20, 19, 21, 18, 21,
      19, 21, 18, 21, 19, 21, 18, 21, 19, 20, 20, 20, 19, 20, 20, 19, 20, 20, 20, 19, 20, 20, 20,
      19, 21, 18, 21, 19, 20, 20, 20, 19, 20, 20, 20, 19, 20, 20, 19, 20, 20, 20, 19, 21, 18,
      21] := by
  have h : ∀ i ∈ List.range 69, a (i + 2) = ((cK (i + 2) : ℤ) - cK (i + 1)) := by
    intro i hi
    rw [List.mem_range] at hi
    rw [a, c_eq (i + 2) (by omega) (by omega), show i + 2 - 1 = i + 1 by omega,
      c_eq (i + 1) (by omega) (by omega)]
  rw [List.map_congr_left h]
  decide +kernel

/-! ### `c n` is a genuine count -/

theorem S_ge (k : ℕ) (hk : 2 ≤ k) : (5 / 6 : ℝ) * √(k : ℝ) ≤ S k := by
  obtain ⟨hx0, hx1, hx2⟩ := inv_sqrt_facts k hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  -- each term is at least `arctan (1/√k)`
  have h1 : (k : ℝ) * arctan (1 / √(k : ℝ)) ≤ S k := by
    have : ∑ _i ∈ range k, arctan (1 / √(k : ℝ)) ≤ S k := by
      refine sum_le_sum fun i hi => ?_
      rw [mem_range] at hi
      refine arctan_strictMono.monotone ?_
      have hi' : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
      exact one_div_le_one_div_of_le (by positivity) (Real.sqrt_le_sqrt hi')
    simpa using this
  -- `arctan x ≥ x (1 - 1/(3k)) ≥ (5/6) x`
  set x := 1 / √(k : ℝ) with hx
  have h2 := (arctan_alt_bounds hx0 hx1 1).1
  rw [alt_sum_even hx2] at h2
  have hA : serA (k : ℝ) 1 = 1 := by simp [serA]
  have hB : serB (k : ℝ) 1 = (k : ℝ)⁻¹ / 3 := by simp [serB]
  rw [hA, hB] at h2
  have hkinv : (k : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hk0 (by norm_num)]; linarith
  have h3 : (5 / 6 : ℝ) * x ≤ arctan x := by nlinarith [mul_le_mul_of_nonneg_left hkinv hx0]
  have h4 : (k : ℝ) * x = √(k : ℝ) := by
    rw [hx, mul_one_div, Real.div_sqrt]
  nlinarith [h1, h3, h4, hk0]

theorem turnTriangles_finite (n : ℕ) : (turnTriangles n).Finite := by
  refine (Set.finite_Iio (81 * n ^ 2 + 2)).subset fun i hi => ?_
  obtain ⟨-, -, hi⟩ := hi
  simp only [Set.mem_Iio]
  by_contra hlt
  have hi2 : 2 ≤ i := by omega
  have h1 := S_ge i hi2
  have hpi := Real.pi_lt_d2
  have hn : (0 : ℝ) ≤ n := by positivity
  have h2 : √(i : ℝ) ≤ 9 * n := by nlinarith [Real.sqrt_nonneg (i : ℝ)]
  have h3 : (i : ℝ) ≤ (9 * n) ^ 2 := by
    rw [← Real.sq_sqrt (Nat.cast_nonneg i)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  have h4 : (i : ℝ) < 81 * n ^ 2 + 2 := by nlinarith
  have : i < 81 * n ^ 2 + 2 := by exact_mod_cast h4
  omega

/-! ### The conjecture -/

/-- The conjecture of A172164: every term `a n` (`n ≥ 2`) is one of `18, 19, 20, 21`. -/
def statement : Prop := ∀ n : ℕ, 2 ≤ n → a n = 18 ∨ a n = 19 ∨ a n = 20 ∨ a n = 21

end Math0.Statements.A172164
