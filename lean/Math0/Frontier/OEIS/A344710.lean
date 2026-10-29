/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A344710
import Math0.Audit

/-!
# A344710: every non-obtuse lattice triangle with sides `≥ √n` has `|det| > (√3/2) n`

We prove Waldmann's conjectured inequality `a(n) > √(3/4) · n` for all `n ≥ 1`.

Let `X, Y, Z` be the squared side lengths of an admissible triangle and `D = det2 A B C`. Then
`4 D² = 2XY + 2YZ + 2ZX - X² - Y² - Z²` (Heron / Lagrange identity). If `Z` is the largest of
the three, this equals `4XY - (X + Y - Z)²`, and non-obtuseness gives `0 ≤ X + Y - Z ≤ min(X, Y)`,
so `(X + Y - Z)² ≤ XY` and `4 D² ≥ 3XY ≥ 3n²`. Equality `4D² = 3n²` with `n ≥ 1` is impossible
because `√3` is irrational. Hence `4 a(n)² > 3 n²`, i.e. `a(n) > √(3/4) · n`.
-/

namespace Math0.Frontier.A344710
open Math0.Statements.A344710

/-- The key inequality in the case where `Z` is the largest squared side. -/
private lemma heron_bound_of_max (X Y Z n : ℤ) (hn : 0 ≤ n) (hX : n ≤ X) (hY : n ≤ Y)
    (h0 : 0 ≤ X + Y - Z) (hZX : X ≤ Z) (hZY : Y ≤ Z) :
    3 * n ^ 2 ≤ 2 * X * Y + 2 * Y * Z + 2 * Z * X - X ^ 2 - Y ^ 2 - Z ^ 2 := by
  have h1 : (X + Y - Z) * (X + Y - Z) ≤ X * Y :=
    mul_le_mul (by linarith) (by linarith) h0 (by linarith)
  have h2 : n * n ≤ X * Y := mul_le_mul hX hY hn (by linarith)
  nlinarith

/-- Heron-type lower bound: for squared side lengths `X, Y, Z ≥ n ≥ 0` of a non-obtuse triangle,
`16 · area² = 2XY + 2YZ + 2ZX - X² - Y² - Z² ≥ 3 n²`. -/
private lemma heron_bound (X Y Z n : ℤ) (hn : 0 ≤ n) (hX : n ≤ X) (hY : n ≤ Y) (hZ : n ≤ Z)
    (h1 : 0 ≤ X + Y - Z) (h2 : 0 ≤ X + Z - Y) (h3 : 0 ≤ Y + Z - X) :
    3 * n ^ 2 ≤ 2 * X * Y + 2 * Y * Z + 2 * Z * X - X ^ 2 - Y ^ 2 - Z ^ 2 := by
  rcases le_total X Z with hXZ | hZX
  · rcases le_total Y Z with hYZ | hZY
    · exact heron_bound_of_max X Y Z n hn hX hY h1 hXZ hYZ
    · -- `Y` is the largest
      have := heron_bound_of_max X Z Y n hn hX hZ h2 (by linarith) hZY
      linarith
  · rcases le_total Y X with hYX | hXY
    · -- `X` is the largest
      have := heron_bound_of_max Y Z X n hn hY hZ h3 hYX hZX
      linarith
    · -- `Y` is the largest
      have := heron_bound_of_max X Z Y n hn hX hZ h2 hXY (by linarith)
      linarith

/-- `4 det² ≥ 3 n²` for every admissible triangle. -/
private lemma det_sq_ge {n : ℕ} {A B C : ℤ × ℤ} (h : IsValid n A B C) :
    3 * (n : ℤ) ^ 2 ≤ 4 * (det2 A B C) ^ 2 := by
  obtain ⟨-, hAB, hBC, hCA, hdA, hdB, hdC⟩ := h
  have hA : 2 * dotAt A B C = dist2 A B + dist2 C A - dist2 B C := by
    simp only [dotAt, dist2]; ring
  have hB : 2 * dotAt B C A = dist2 A B + dist2 B C - dist2 C A := by
    simp only [dotAt, dist2]; ring
  have hC : 2 * dotAt C A B = dist2 B C + dist2 C A - dist2 A B := by
    simp only [dotAt, dist2]; ring
  have hid : 4 * (det2 A B C) ^ 2 =
      2 * dist2 A B * dist2 C A + 2 * dist2 C A * dist2 B C + 2 * dist2 B C * dist2 A B
        - dist2 A B ^ 2 - dist2 C A ^ 2 - dist2 B C ^ 2 := by
    simp only [det2, dist2]; ring
  rw [hid]
  exact heron_bound _ _ _ _ (Int.natCast_nonneg n) hAB hCA hBC (by linarith) (by linarith)
    (by linarith)

/-- `4 m² = 3 n²` has no solution in natural numbers with `n ≥ 1`, since `√3` is irrational. -/
private lemma four_sq_ne_three_sq (m n : ℕ) (hn : 1 ≤ n) : 4 * m ^ 2 ≠ 3 * n ^ 2 := by
  intro h
  have hirr : Irrational (√((3 : ℕ) : ℝ)) := Nat.prime_three.irrational_sqrt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : ((2 * m : ℕ) : ℝ) ^ 2 = (3 : ℝ) * (n : ℝ) ^ 2 := by
    have : ((4 * m ^ 2 : ℕ) : ℝ) = ((3 * n ^ 2 : ℕ) : ℝ) := by rw [h]
    push_cast at this ⊢
    linarith
  have hs : √((3 : ℕ) : ℝ) * n = ((2 * m : ℕ) : ℝ) := by
    rw [← Real.sqrt_sq hnR.le, ← Real.sqrt_mul (by norm_num), Nat.cast_ofNat, ← hR,
      Real.sqrt_sq (by positivity)]
  have hq : √((3 : ℕ) : ℝ) = ((2 * m : ℕ) : ℤ) / ((n : ℕ) : ℤ) := by
    have hn' : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hnR.ne'
    push_cast at hs hn' ⊢
    rw [eq_div_iff hn']
    exact hs
  exact (irrational_iff_ne_rational _).mp hirr _ _ (by exact_mod_cast (by omega : n ≠ 0)) hq

/-- Waldmann's conjecture A344710: `a(n) > √(3/4) · n` for every `n ≥ 1`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨⟨A, B, C, hv, hk⟩, -⟩ := isLeast_a n
  have hge := det_sq_ge hv
  have hsq : (det2 A B C) ^ 2 = ((a n : ℕ) : ℤ) ^ 2 := by
    rw [← hk, Int.natCast_natAbs, sq_abs]
  rw [hsq] at hge
  have hgeN : 3 * n ^ 2 ≤ 4 * (a n) ^ 2 := by exact_mod_cast hge
  have hlt : 3 * n ^ 2 < 4 * (a n) ^ 2 :=
    lt_of_le_of_ne hgeN (fun h => four_sq_ne_three_sq (a n) n hn h.symm)
  have hltR : (3 : ℝ) * (n : ℝ) ^ 2 < 4 * ((a n : ℕ) : ℝ) ^ 2 := by exact_mod_cast hlt
  have hapos : (0 : ℝ) < (a n : ℝ) := by
    rcases Nat.eq_zero_or_pos (a n) with h0 | h0
    · rw [h0] at hltR
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      nlinarith
    · exact_mod_cast h0
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [← Real.sqrt_sq hnR, ← Real.sqrt_mul (by norm_num), Real.sqrt_lt' hapos]
  linarith
end Math0.Frontier.A344710

#math0_settles Math0.Frontier.A344710.result Math0.Statements.A344710.statement
