/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A392943
import Math0.Audit

/-!
# No primitive Heronian triangle has integer circumradius

We prove Felix Huber's conjecture from OEIS A392943: if a triangle has integer sides `x, y, z`,
integer area `K` and integer circumradius `R` (`4 K R = x y z`), then `x`, `y`, `z` are all
even, so `gcd(x, y, z) ≠ 1`.

Idea: write `P = 16 K²` (Heron) and `D = y² + z² - x²`. Then `P = 4 y² z² - D²`, and squaring
`4 K R = x y z` gives `P R² = x² y² z²`, i.e. `(y z)² (4 R² - x²) = (R D)²`. Hence `(y z)² ∣ (R D)²`,
so `y z ∣ R D`; writing `R D = y z m` and cancelling `(y z)² ≠ 0` gives `x² + m² = 4 R²`.
Squares are `0` or `1` mod `4`, so `x` is even. By symmetry `y` and `z` are even too.
Integrality of the area is only used through `P R² = (x y z)²`.
-/

namespace Math0.Frontier.A392943
open Math0.Statements.A392943

/-- If `P(a,b,c) R² = (a b c)²` with `P` the Heron product and `b, c ≠ 0`, then `a` is even. -/
private theorem two_dvd_of_heron (a b c R : ℤ) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) * R ^ 2 = (a * b * c) ^ 2) :
    2 ∣ a := by
  have h1 : (b * c) ^ 2 * (4 * R ^ 2 - a ^ 2) = (R * (b ^ 2 + c ^ 2 - a ^ 2)) ^ 2 := by
    linear_combination h
  have hdvd : (b * c) ^ 2 ∣ (R * (b ^ 2 + c ^ 2 - a ^ 2)) ^ 2 := ⟨_, h1.symm⟩
  obtain ⟨m, hm⟩ := (Int.pow_dvd_pow_iff (by norm_num)).1 hdvd
  have hbc : (b * c) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hb hc)
  have h2 : (b * c) ^ 2 * (4 * R ^ 2 - a ^ 2) = (b * c) ^ 2 * m ^ 2 := by
    rw [h1, hm]; ring
  have h3 : a ^ 2 + m ^ 2 = 4 * R ^ 2 := by
    have := mul_left_cancel₀ hbc h2
    linear_combination -this
  by_contra hodd
  have ha : Odd a := Int.not_even_iff_odd.1 (fun he => hodd (even_iff_two_dvd.1 he))
  have ha2 : a ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd ha
  have h4 : (a ^ 2 + m ^ 2) % 4 = 0 := by rw [h3]; simp
  rcases Int.even_or_odd m with ⟨j, rfl⟩ | hm'
  · have hm2 : (j + j) ^ 2 = 4 * (j ^ 2) := by ring
    rw [hm2] at h4
    omega
  · have hm2 : m ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd hm'
    omega

/-- Every primitive Heronian triangle has non-integer circumradius: if `4 K R = x y z` for a
triangle with integer sides `x, y, z` and integer area `K`, then `2 ∣ gcd(x, y, z)`. -/
theorem result : statement := by
  intro x y z K R htri hK hgcd hR
  obtain ⟨hx, hy, hz, -, -, -⟩ := htri
  rw [HasArea, heron16] at hK
  have hRz : ((4 * K * R : ℕ) : ℤ) = ((x * y * z : ℕ) : ℤ) := by rw [hR]
  push_cast at hRz
  have key : ((x : ℤ) + y + z) * (-x + y + z) * (x - y + z) * (x + y - z) * (R : ℤ) ^ 2 =
      ((x : ℤ) * y * z) ^ 2 := by
    rw [← hK, ← hRz]; ring
  have hx0 : (x : ℤ) ≠ 0 := by exact_mod_cast hx.ne'
  have hy0 : (y : ℤ) ≠ 0 := by exact_mod_cast hy.ne'
  have hz0 : (z : ℤ) ≠ 0 := by exact_mod_cast hz.ne'
  have h2x : (2 : ℤ) ∣ x := two_dvd_of_heron x y z R hy0 hz0 key
  have h2y : (2 : ℤ) ∣ y := two_dvd_of_heron y x z R hx0 hz0 (by linear_combination key)
  have h2z : (2 : ℤ) ∣ z := two_dvd_of_heron z x y R hx0 hy0 (by linear_combination key)
  have h2x' : 2 ∣ x := by exact_mod_cast h2x
  have h2y' : 2 ∣ y := by exact_mod_cast h2y
  have h2z' : 2 ∣ z := by exact_mod_cast h2z
  have : 2 ∣ Nat.gcd x (Nat.gcd y z) := Nat.dvd_gcd h2x' (Nat.dvd_gcd h2y' h2z')
  rw [hgcd] at this
  omega

end Math0.Frontier.A392943

#math0_settles Math0.Frontier.A392943.result Math0.Statements.A392943.statement
