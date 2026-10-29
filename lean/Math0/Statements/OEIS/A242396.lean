/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A242396: rows of unit triangles meeting a circle of radius n

Source: https://oeis.org/A242396, _Ralf Stephan_, May 18 2014 (entry by _Kival Ngaokrajang_,
May 13 2014). Verbatim (FORMULA section):
> G.f., conjectured: (-2*x^14 + 4*x^13 + 2*x^12 + 2*x^11 + 2*x^10 + 2*x^9 + 2*x^8 + 4*x^7 +
> 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 4*x)/(x^14 - x^13 - x + 1). - _Ralf Stephan_, May 18 2014

The next FORMULA line is a consequence drawn from that conjectured g.f.; verbatim:
> Asymptotics from g.f.: a(n) ~ 30/13 * n. - _Ralf Stephan_, May 18 2014

The entry's name: "Number of rows of equilateral triangles (sides length = 1) that intersect the
circumference of a circle of radius n centered at (0,0) or (1/2,0)." Offset `1`.

## Encoding

* The tiling is the tiling of the plane by equilateral triangles of side `1` with a vertex at
  the origin and horizontal sides, as in the entry's Small Basic program and in the sibling
  entries A242394 / A242395 (whose programs place the tiling vertices at `(j/2, i·√3/2)`). Its
  rows are the closed horizontal strips `{(x, y) | j·√3/2 ≤ y ≤ (j+1)·√3/2}`, `j ∈ ℤ`; the
  triangles of row `j` tile exactly that strip, so a row meets the circle iff the strip does.
* `RowMeets c n j` says that the circle `(x - c)² + y² = n²` (center `(c, 0)`) meets row `j`.
  The name allows the center `(0,0)` or `(1/2,0)`; `rowMeets_iff` shows the condition does not
  depend on `c`, so both readings give the same count.
* `MeetsInt n j` is the decidable integer form of `j·√3/2 ≤ n ∧ -n ≤ (j+1)·√3/2`, namely
  `(j ≤ 0 ∨ 3 j² ≤ 4 n²) ∧ (0 ≤ j + 1 ∨ 3 (j+1)² ≤ 4 n²)`.
* `a n` counts the `i < 4n + 5` with `MeetsInt n (i - (2n+2))`, i.e. the rows
  `j ∈ [-(2n+2), 2n+2]` with `MeetsInt n j` (all meeting rows lie in that range, by
  `bounds_of_meetsInt`); `a_eq_ncard` proves
  `a n = #{j : ℤ | RowMeets c n j}` for every real `c` (in particular `c = 0` and `c = 1/2`),
  so `a` is the OEIS definition, not a closed form.
* Rows are taken closed. For `n ≥ 1` this is immaterial: `2n/√3` is irrational, so no row
  boundary `y = j·√3/2` is tangent to the circle, and every boundary line that meets the circle
  crosses it, entering the interiors of both adjacent rows.
* Offset `1`: `a 0` (here `2`) is not a term of the sequence. The conjectured g.f. has no
  constant term (its numerator is divisible by `x` and its denominator has constant term `1`),
  so it is read as `∑_{n ≥ 1} a(n) xⁿ`; the series in `statement` therefore has coefficient `0`
  at `x⁰` and `a n` at `xⁿ` for `n ≥ 1`.
* `statement` is the g.f. identity in `ℤ⟦X⟧` with the denominator cleared. The denominator
  `x¹⁴ - x¹³ - x + 1` has constant coefficient `1`, hence is a unit of `ℤ⟦X⟧`, so this is
  equivalent to the stated equality of the series with the quotient.
* `statement_asymptotic` records the derived asymptotic claim `a(n) ~ 30/13 · n`
  (`Asymptotics.IsEquivalent` along `atTop`); it is not part of `statement`.
-/

namespace Math0.Statements.A242396

open Real

/-- Row `j : ℤ` of the unit triangular tiling (the closed strip
`j·√3/2 ≤ y ≤ (j+1)·√3/2`) meets the circle of radius `n` centered at `(c, 0)`. -/
def RowMeets (c : ℝ) (n : ℕ) (j : ℤ) : Prop :=
  ∃ x y : ℝ, (x - c) ^ 2 + y ^ 2 = (n : ℝ) ^ 2 ∧
    (j : ℝ) * (√3 / 2) ≤ y ∧ y ≤ ((j : ℝ) + 1) * (√3 / 2)

/-- Integer form of `j·√3/2 ≤ n ∧ -n ≤ (j+1)·√3/2` (see `rowMeets_iff`). -/
def MeetsInt (n : ℕ) (j : ℤ) : Prop :=
  (j ≤ 0 ∨ 3 * j ^ 2 ≤ 4 * (n : ℤ) ^ 2) ∧ (0 ≤ j + 1 ∨ 3 * (j + 1) ^ 2 ≤ 4 * (n : ℤ) ^ 2)

instance (n : ℕ) : DecidablePred (MeetsInt n) := fun _ => by
  unfold MeetsInt; infer_instance

/-- A242396: the number of rows of the unit equilateral-triangle tiling that meet the circle of
radius `n` centered at `(0,0)` (or `(1/2,0)`). Row `j` is indexed by `i = j + 2n + 2 < 4n + 5`,
i.e. `j` ranges over `[-(2n+2), 2n+2]`, which contains every meeting row; see `a_eq_ncard`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (4 * n + 5)).filter (fun i : ℕ => MeetsInt n ((i : ℤ) - (2 * n + 2)))).card

/-- The definition reproduces the first terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 61).map (fun i => a (i + 1)) =
    [4, 6, 8, 10, 12, 14, 18, 20, 22, 24, 26, 28, 32, 34, 36, 38, 40, 42, 44, 48, 50, 52, 54, 56,
     58, 62, 64, 66, 68, 70, 72, 74, 78, 80, 82, 84, 86, 88, 92, 94, 96, 98, 100, 102, 104,
     108, 110, 112, 114, 116, 118, 122, 124, 126, 128, 130, 132, 134, 138, 140, 142] := by
  decide +kernel

/-! ### `a` is the geometric count -/

theorem mul_half_sqrt_three_le_iff (k : ℤ) (n : ℕ) :
    (k : ℝ) * (√3 / 2) ≤ n ↔ k ≤ 0 ∨ 3 * k ^ 2 ≤ 4 * (n : ℤ) ^ 2 := by
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have hs : 0 ≤ √3 := sqrt_nonneg 3
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · intro h
    by_cases hk : k ≤ 0
    · exact Or.inl hk
    · right
      push Not at hk
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have h1 : (k : ℝ) * √3 ≤ 2 * n := by linarith
      have h2 : ((k : ℝ) * √3) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      have h4 : ((3 * k ^ 2 : ℤ) : ℝ) ≤ ((4 * (n : ℤ) ^ 2 : ℤ) : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast h4
  · rintro (hk | hk)
    · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      have : (k : ℝ) * (√3 / 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk' (by positivity)
      linarith
    · have hk' : ((3 * k ^ 2 : ℤ) : ℝ) ≤ ((4 * (n : ℤ) ^ 2 : ℤ) : ℝ) := by exact_mod_cast hk
      push_cast at hk'
      by_contra hlt
      push Not at hlt
      have h1 : 2 * (n : ℝ) < (k : ℝ) * √3 := by linarith
      have h2 : (2 * (n : ℝ)) ^ 2 < ((k : ℝ) * √3) ^ 2 :=
        pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
      nlinarith

theorem rowMeets_iff_real (c : ℝ) (n : ℕ) (j : ℤ) :
    RowMeets c n j ↔ (j : ℝ) * (√3 / 2) ≤ n ∧ -(n : ℝ) ≤ ((j : ℝ) + 1) * (√3 / 2) := by
  have hs : 0 ≤ √3 / 2 := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · rintro ⟨x, y, hxy, h1, h2⟩
    have hy : y ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg (x - c)]
    obtain ⟨hy1, hy2⟩ := abs_le_of_sq_le_sq' hy hn
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    set y := max ((j : ℝ) * (√3 / 2)) (-(n : ℝ)) with hy
    have hy1 : (j : ℝ) * (√3 / 2) ≤ y := le_max_left _ _
    have hy2 : -(n : ℝ) ≤ y := le_max_right _ _
    have hy3 : y ≤ n := max_le h1 (by linarith)
    have hy4 : y ≤ ((j : ℝ) + 1) * (√3 / 2) := max_le (by nlinarith) h2
    have hnn : 0 ≤ (n : ℝ) ^ 2 - y ^ 2 := by nlinarith
    refine ⟨c + √((n : ℝ) ^ 2 - y ^ 2), y, ?_, hy1, hy4⟩
    rw [add_sub_cancel_left, sq_sqrt hnn]
    ring

/-- The geometric condition is equivalent to the integer condition `MeetsInt`, for every
center `(c, 0)`. -/
theorem rowMeets_iff (c : ℝ) (n : ℕ) (j : ℤ) : RowMeets c n j ↔ MeetsInt n j := by
  rw [rowMeets_iff_real, MeetsInt, mul_half_sqrt_three_le_iff]
  have : -(n : ℝ) ≤ ((j : ℝ) + 1) * (√3 / 2) ↔ ((-(j + 1) : ℤ) : ℝ) * (√3 / 2) ≤ n := by
    push_cast
    constructor <;> intro h <;> linarith
  rw [this, mul_half_sqrt_three_le_iff, neg_nonpos, neg_sq]

theorem bounds_of_meetsInt {n : ℕ} {j : ℤ} (h : MeetsInt n j) :
    -(2 * (n : ℤ) + 2) ≤ j ∧ j ≤ 2 * n + 2 := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  obtain ⟨h1 | h1, h2 | h2⟩ := h <;> constructor <;> nlinarith

/-- `a n` is the number of rows `j : ℤ` meeting the circle of radius `n` centered at `(c, 0)`,
for any `c` (in particular for the centers `(0,0)` and `(1/2,0)` of the OEIS name). -/
theorem a_eq_ncard (c : ℝ) (n : ℕ) : a n = {j : ℤ | RowMeets c n j}.ncard := by
  have hset : {j : ℤ | RowMeets c n j} =
      ↑(((Finset.range (4 * n + 5)).filter
        (fun i : ℕ => MeetsInt n ((i : ℤ) - (2 * n + 2)))).image
          (fun i : ℕ => (i : ℤ) - (2 * n + 2))) := by
    ext j
    simp only [Set.mem_ofPred_eq, rowMeets_iff, Finset.coe_image, Finset.coe_filter,
      Finset.mem_range, Set.mem_image]
    constructor
    · intro hj
      obtain ⟨hb1, hb2⟩ := bounds_of_meetsInt hj
      refine ⟨(j + (2 * n + 2)).toNat, ⟨?_, ?_⟩, ?_⟩
      · omega
      · rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel_right]
      · rw [Int.toNat_of_nonneg (by omega), add_sub_cancel_right]
    · rintro ⟨i, ⟨_, hi⟩, rfl⟩
      exact hi
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ (fun i i' h => by
    simpa using h)]
  rfl

/-! ### The conjecture -/

open PowerSeries in
/-- Stephan's conjectured g.f., as an identity in `ℤ⟦X⟧` with the denominator cleared:
`(∑_{n ≥ 1} a(n) xⁿ) · (x¹⁴ - x¹³ - x + 1) = -2x¹⁴ + 4x¹³ + 2x¹² + 2x¹¹ + 2x¹⁰ + 2x⁹ + 2x⁸ +
4x⁷ + 2x⁶ + 2x⁵ + 2x⁴ + 2x³ + 2x² + 4x`. -/
def statement : Prop :=
  PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 14 - X ^ 13 - X + 1) =
    -2 * X ^ 14 + 4 * X ^ 13 + 2 * X ^ 12 + 2 * X ^ 11 + 2 * X ^ 10 + 2 * X ^ 9 + 2 * X ^ 8 +
      4 * X ^ 7 + 2 * X ^ 6 + 2 * X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + 2 * X ^ 2 + 4 * X

/-- The asymptotic claim drawn from the conjectured g.f.: `a(n) ~ 30/13 · n`.
Not part of `statement`. -/
def statement_asymptotic : Prop :=
  Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ)) (fun n => 30 / 13 * (n : ℝ))

end Math0.Statements.A242396
