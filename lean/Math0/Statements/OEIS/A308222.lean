/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A308222: perimeters of primitive Heronian isosceles triangles

Source: https://oeis.org/A308222, _Peter Kagey_, May 16 2019 (FORMULA section). Verbatim:
> a(n) = 2*A096033(n+2) (conjectured).

The entry's name: "Numbers that are the perimeter of a primitive Heronian isosceles triangle."
Comment: "A primitive Heronian triangle is a triangle with integer sides and area, where the
side lengths do not share a common divisor." Offset `1`: `a(1) = 16`, from `(5, 5, 6)`.
A096033 is "Difference between leg and hypotenuse in primitive Pythagorean triangles", offset `1`:
`1, 2, 8, 9, 18, …`.

## Encoding

* *Triangles.* Sides are natural numbers `x, y, z` with the strict triangle inequalities
  `x < y + z`, `y < x + z`, `z < x + y` (non-degenerate, so all sides are `≥ 1`).
* *Heronian.* The area is an integer `A`. By Heron's formula
  `16 · area² = (x+y+z)(-x+y+z)(x-y+z)(x+y-z)` (`heron`, computed in `ℤ`), so this says
  `16 A² = heron x y z` for some `A : ℕ` (`IsHeronian`).
* *Primitive.* `gcd(gcd(x, y), z) = 1` (`IsPrimitive`). *Isosceles.* Two sides are equal
  (`IsIsosceles`). An equilateral triangle counts too, but none is Heronian.
* *The sequence.* `IsPerimeter P`: some such triangle has `x + y + z = P`. The entry lists each
  perimeter once, in increasing order (e.g. `50` comes from both `(13,13,24)` and `(16,17,17)`),
  so `a n = Nat.nth IsPerimeter (n - 1)` is the `n`-th smallest perimeter (offset `1`).
* *Deciding `IsPerimeter`.* `Nat.nth` is noncomputable, so `IsPerimeter` is made decidable by
  `perimB`, a bounded search proved equivalent to it (`perimB_iff`). A triangle is written with
  legs `s, s` and base `b` (`isPerimeter_iff`). Its base is even and its legs are odd
  (`IsoOK.base_even`, `IsoOK.leg_odd`). So `P = 2m`, `b = 2(m - s)`, and the area is an integer
  iff `m (2s - m)` is a square (`isoOK_iff_legOK`). The search runs over the odd `s` with
  `m/2 < s < m`. Squares are recognized by a quadratic-residue filter and a certified integer
  square root (`sqB_iff`). These are elementary rewritings of the definition, used only to
  evaluate it.
* *A096033.* `IsLegHypDiff d`: there are legs `x, y ≥ 1` with `gcd(x, y) = 1` and a hypotenuse
  `z` with `x² + y² = z²` and `z = x + d` (`x` may be either leg). `A096033 n` is the `n`-th
  smallest such `d` (offset `1`). For decidability, `isLegHypDiff_iff` proves the
  characterization stated in A096033 itself (odd squares and the numbers `2 j²`, `j ≥ 1`), using
  Mathlib's classification of primitive Pythagorean triples. This concerns only A096033 and does
  not touch the conjecture.
* *Data.* `a_data` checks all 46 listed terms of A308222 (`a(1..46)`, up to `3136`) in the
  kernel. The search below `3137` is split into 7 separate kernel checks (`chunk_1`, …,
  `chunk_7`) to bound memory. `A096033_data` checks the 52 listed terms of A096033.
* *The conjecture.* `statement`: for every `n ≥ 1`, `a(n) = 2 · A096033(n + 2)`.
-/

namespace Math0.Statements.A308222

/-! ### Primitive Heronian isosceles triangles -/

/-- Heron's product `(x+y+z)(-x+y+z)(x-y+z)(x+y-z)`. It equals `16 · area²` for the triangle with
sides `x, y, z`. -/
def heron (x y z : ℤ) : ℤ := (x + y + z) * (-x + y + z) * (x - y + z) * (x + y - z)

/-- `x, y, z` are the sides of a Heronian triangle: a non-degenerate triangle (strict triangle
inequalities) with integer sides whose area is an integer `A`, i.e. `16 A² = heron x y z`. -/
def IsHeronian (x y z : ℕ) : Prop :=
  x < y + z ∧ y < x + z ∧ z < x + y ∧ ∃ A : ℕ, 16 * (A : ℤ) ^ 2 = heron x y z

/-- The side lengths `x, y, z` have no common divisor greater than `1`. -/
def IsPrimitive (x y z : ℕ) : Prop := Nat.gcd (Nat.gcd x y) z = 1

/-- Two of the sides `x, y, z` are equal. -/
def IsIsosceles (x y z : ℕ) : Prop := x = y ∨ y = z ∨ x = z

/-- `P` is the perimeter of a primitive Heronian isosceles triangle. -/
def IsPerimeter (P : ℕ) : Prop :=
  ∃ x y z : ℕ, IsHeronian x y z ∧ IsPrimitive x y z ∧ IsIsosceles x y z ∧ x + y + z = P

/-- A308222 (offset `1`): the `n`-th smallest perimeter of a primitive Heronian isosceles
triangle. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsPerimeter (n - 1)

/-! ### Deciding `IsPerimeter` -/

/-! The decision procedure uses only `Bool`-valued primitives (`Nat.blt`, `Nat.beq`, `cond`),
which keeps kernel evaluation cheap. -/

/-- Newton iteration for `⌊√n⌋` with fuel. It is only a guess, certified in `sqAt`. -/
def sqrtIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | fuel + 1, n, g =>
    bif Nat.blt ((g + n / g) / 2) g then sqrtIter fuel n ((g + n / g) / 2) else g

/-- A guess for `⌊√n⌋`. -/
def sqrtGuess (n : ℕ) : ℕ := sqrtIter 64 n (2 ^ (Nat.log2 n / 2 + 1))

/-- Decides whether `n` is a perfect square, given a guess `r` for `⌊√n⌋`: if
`r² ≤ n < (r+1)²` then `n` is a square iff `r² = n`; otherwise an exhaustive search. -/
def sqAt (n r : ℕ) : Bool :=
  bif Nat.ble (r * r) n && Nat.blt n ((r + 1) * (r + 1)) then Nat.beq (r * r) n
  else (List.range (n + 1)).any fun k => Nat.beq (k * k) n

theorem sqAt_iff (n r : ℕ) : sqAt n r = true ↔ ∃ k, k * k = n := by
  unfold sqAt
  cases h : (Nat.ble (r * r) n && Nat.blt n ((r + 1) * (r + 1)))
  · simp only [cond_false, List.any_eq_true, List.mem_range, Nat.beq_eq]
    constructor
    · rintro ⟨k, -, hk⟩
      exact ⟨k, hk⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by have := Nat.le_mul_self k; omega, rfl⟩
  · simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    simp only [cond_true, Nat.beq_eq]
    constructor
    · intro h'
      exact ⟨r, h'⟩
    · rintro ⟨k, rfl⟩
      have h1 : r ≤ k := Nat.mul_self_le_mul_self_iff.1 h.1
      have h2 : k < r + 1 := Nat.mul_self_lt_mul_self_iff.1 h.2
      rw [show r = k by omega]

/-- Bit number `n % m` of the mask `M` (used with `M` = the set of squares modulo `m`). -/
def qr (M m n : ℕ) : Bool := Nat.beq ((M >>> (n % m)) % 2) 1

theorem qr_mul_self {M m : ℕ} (hm : 0 < m) (h : ∀ r < m, qr M m (r * r) = true) (k : ℕ) :
    qr M m (k * k) = true := by
  have := h (k % m) (Nat.mod_lt _ hm)
  unfold qr at *
  rwa [← Nat.mul_mod] at this

/-- Decides whether `n` is a perfect square: a quick test that `n` is a square modulo `64`,
`63`, `65` and `11` (bit masks of the squares), then `sqAt`. -/
def sqB (n : ℕ) : Bool :=
  qr 144680414395695635 64 n && qr 288872697407275667 63 n && qr 20863489977805260307 65 n &&
    qr 571 11 n && sqAt n (sqrtGuess n)

theorem sqB_iff (n : ℕ) : sqB n = true ↔ ∃ k, k * k = n := by
  constructor
  · intro h
    simp only [sqB, Bool.and_eq_true] at h
    exact (sqAt_iff _ _).1 h.2
  · rintro ⟨k, rfl⟩
    simp only [sqB, Bool.and_eq_true]
    refine ⟨⟨⟨⟨qr_mul_self (by norm_num) (by decide) k, qr_mul_self (by norm_num) (by decide) k⟩,
      qr_mul_self (by norm_num) (by decide) k⟩, qr_mul_self (by norm_num) (by decide) k⟩,
      (sqAt_iff _ _).2 ⟨k, rfl⟩⟩

/-- The triangle with legs `s, s` and base `b` is a primitive Heronian triangle (in `ℕ`). -/
def IsoOK (s b : ℕ) : Prop :=
  0 < b ∧ b < 2 * s ∧ Nat.gcd s b = 1 ∧ ∃ A : ℕ, 16 * A ^ 2 = (2 * s + b) * b * b * (2 * s - b)

theorem heron_iso {s b : ℕ} (h : b < 2 * s) :
    heron s s b = (((2 * s + b) * b * b * (2 * s - b) : ℕ) : ℤ) := by
  unfold heron
  push_cast [Nat.cast_sub h.le]
  ring

theorem isoOK_of {s b : ℕ} (hH : IsHeronian s s b) (hg : Nat.gcd s b = 1) : IsoOK s b := by
  obtain ⟨h1, -, h3, A, hA⟩ := hH
  refine ⟨by omega, by omega, hg, A, ?_⟩
  rw [heron_iso (by omega)] at hA
  exact_mod_cast hA

/-- Every primitive Heronian isosceles triangle can be written with legs `s, s` and base `b`. -/
theorem isPerimeter_iff (P : ℕ) : IsPerimeter P ↔ ∃ s b, IsoOK s b ∧ 2 * s + b = P := by
  constructor
  · rintro ⟨x, y, z, hH, hp, hi, hP⟩
    rcases hi with rfl | rfl | rfl
    · refine ⟨x, z, isoOK_of hH ?_, by omega⟩
      simpa [IsPrimitive] using hp
    · refine ⟨y, x, isoOK_of ?_ ?_, by omega⟩
      · obtain ⟨h1, h2, h3, A, hA⟩ := hH
        refine ⟨by omega, by omega, by omega, A, ?_⟩
        rw [hA]; unfold heron; ring
      · have : Nat.gcd (Nat.gcd x y) y = Nat.gcd y x := by
          rw [Nat.gcd_assoc, Nat.gcd_self, Nat.gcd_comm]
        rw [← this]; exact hp
    · refine ⟨x, y, isoOK_of ?_ ?_, by omega⟩
      · obtain ⟨h1, h2, h3, A, hA⟩ := hH
        refine ⟨by omega, by omega, by omega, A, ?_⟩
        rw [hA]; unfold heron; ring
      · have : Nat.gcd (Nat.gcd x y) x = Nat.gcd x y := by
          rw [Nat.gcd_comm, ← Nat.gcd_assoc, Nat.gcd_self]
        rw [← this]; exact hp
  · rintro ⟨s, b, ⟨h0, h1, hg, A, hA⟩, hP⟩
    refine ⟨s, s, b, ⟨by omega, by omega, by omega, A, ?_⟩, by simpa [IsPrimitive] using hg,
      Or.inl rfl, by omega⟩
    rw [heron_iso h1]
    exact_mod_cast hA

/-- The base of a Heronian isosceles triangle is even (otherwise `16 A²` would be odd). -/
theorem IsoOK.base_even {s b : ℕ} (h : IsoOK s b) : b % 2 = 0 := by
  obtain ⟨h0, h1, -, A, hA⟩ := h
  by_contra hb
  have e1 : ¬ Even (2 * s + b) := by rw [Nat.even_iff]; omega
  have e2 : ¬ Even (2 * s - b) := by rw [Nat.even_iff]; omega
  have e3 : ¬ Even b := by rw [Nat.even_iff]; omega
  have : Even ((2 * s + b) * b * b * (2 * s - b)) := hA ▸ ⟨8 * A ^ 2, by ring⟩
  simp [Nat.even_mul, e1, e2, e3] at this

/-- Hence the legs of a primitive Heronian isosceles triangle are odd. -/
theorem IsoOK.leg_odd {s b : ℕ} (h : IsoOK s b) : s % 2 = 1 := by
  have hb := h.base_even
  obtain ⟨-, -, hg, -⟩ := h
  by_contra hs
  have h2 : 2 ∣ Nat.gcd s b :=
    Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero hb)
  rw [hg] at h2
  exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)

/-- For `x ≥ 1`, `A² = x² K` has a solution `A` iff `K` is a square. -/
theorem exists_sq_mul_iff {x K : ℕ} (hx : 0 < x) :
    (∃ A : ℕ, A ^ 2 = x ^ 2 * K) ↔ ∃ h, h * h = K := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨h, rfl⟩ : x ∣ A := (Nat.pow_dvd_pow_iff two_ne_zero).1 ⟨K, hA⟩
    refine ⟨h, Nat.eq_of_mul_eq_mul_left (show 0 < x ^ 2 by positivity) ?_⟩
    rw [← hA]; ring
  · rintro ⟨h, rfl⟩
    exact ⟨x * h, by ring⟩

/-- For the perimeter `2m`, the leg `s` (with base `2(m - s)`) gives a primitive Heronian
isosceles triangle: `m/2 < s < m`, `s` odd, `gcd(s, m) = 1`, and `m (2s - m)` is a square. -/
def LegOK (m s : ℕ) : Prop :=
  m < 2 * s ∧ s < m ∧ s % 2 = 1 ∧ Nat.gcd s m = 1 ∧ ∃ h, h * h = m * (2 * s - m)

theorem isoOK_iff_legOK (s x : ℕ) : IsoOK s (2 * x) ↔ LegOK (s + x) s := by
  constructor
  · intro hiso
    have hodd := hiso.leg_odd
    obtain ⟨h0, h1, hg, A, hA⟩ := hiso
    obtain ⟨e, rfl⟩ : ∃ e, s = x + e := ⟨s - x, by omega⟩
    refine ⟨by omega, by omega, hodd, ?_, ?_⟩
    · rw [Nat.gcd_self_add_right]
      exact Nat.Coprime.coprime_mul_left_right hg
    · rw [show 2 * (x + e) - 2 * x = 2 * e by omega] at hA
      rw [show 2 * (x + e) - (x + e + x) = e by omega]
      refine (exists_sq_mul_iff (x := x) (by omega)).1 ⟨A, ?_⟩
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 16 by norm_num)
      rw [hA]; ring
  · rintro ⟨h1, h2, hodd, hg, h, hh⟩
    obtain ⟨e, rfl⟩ : ∃ e, s = x + e := ⟨s - x, by omega⟩
    refine ⟨by omega, by omega, ?_, ?_⟩
    · apply Nat.Coprime.mul_right
      · exact Nat.coprime_two_right.2 (Nat.odd_iff.2 hodd)
      · rw [Nat.gcd_self_add_right] at hg
        exact hg
    · rw [show 2 * (x + e) - (x + e + x) = e by omega] at hh
      obtain ⟨A, hA⟩ := (exists_sq_mul_iff (x := x) (by omega)).2 ⟨h, hh⟩
      refine ⟨A, ?_⟩
      rw [show 2 * (x + e) - 2 * x = 2 * e by omega, hA]
      ring

/-- `P` is a perimeter iff `P = 2m` and some leg `s` works (`LegOK m s`). -/
theorem isPerimeter_iff_legOK (P : ℕ) : IsPerimeter P ↔ P % 2 = 0 ∧ ∃ s, LegOK (P / 2) s := by
  rw [isPerimeter_iff]
  constructor
  · rintro ⟨s, b, hs, hP⟩
    have hb := hs.base_even
    obtain ⟨x, rfl⟩ : ∃ x, b = 2 * x := ⟨b / 2, by omega⟩
    refine ⟨by omega, s, ?_⟩
    rw [show P / 2 = s + x by omega, ← isoOK_iff_legOK]
    exact hs
  · rintro ⟨hP, s, hs⟩
    have h2 := hs.2.1
    refine ⟨s, 2 * (P / 2 - s), ?_, by omega⟩
    rw [isoOK_iff_legOK, show s + (P / 2 - s) = P / 2 by omega]
    exact hs

/-- Boolean version of `LegOK`. -/
def legB (m s : ℕ) : Bool :=
  Nat.beq (Nat.gcd s m) 1 && Nat.blt m (2 * s) && Nat.blt s m && Nat.beq (s % 2) 1 &&
    sqB (m * (2 * s - m))

theorem legB_iff (m s : ℕ) : legB m s = true ↔ LegOK m s := by
  simp only [legB, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, sqB_iff, LegOK]
  constructor
  · rintro ⟨⟨⟨⟨hg, h1⟩, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, hg, h4⟩
  · rintro ⟨h1, h2, h3, hg, h4⟩
    exact ⟨⟨⟨⟨hg, h1⟩, h2⟩, h3⟩, h4⟩

/-- `anyS m k s`: one of the legs `s, s + 2, …, s + 2(k-1)` passes `legB m` (written with
`Nat.rec`, which the kernel evaluates cheaply). -/
def anyS (m k : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false) (fun _ ih s => legB m s || ih (s + 2)) k

theorem anyS_zero (m s : ℕ) : anyS m 0 s = false := rfl

theorem anyS_succ (m k s : ℕ) : anyS m (k + 1) s = (legB m s || anyS m k (s + 2)) := rfl

theorem anyS_iff (m : ℕ) : ∀ k s, anyS m k s = true ↔ ∃ t < k, legB m (s + 2 * t) = true
  | 0, s => by simp [anyS_zero]
  | k + 1, s => by
    rw [anyS_succ, Bool.or_eq_true, anyS_iff m k (s + 2)]
    constructor
    · rintro (h | ⟨t, ht, h⟩)
      · exact ⟨0, by omega, by simpa using h⟩
      · exact ⟨t + 1, by omega, by rw [show s + 2 * (t + 1) = s + 2 + 2 * t by ring]; exact h⟩
    · rintro ⟨t, ht, h⟩
      rcases t with _ | t
      · left
        simpa using h
      · right
        exact ⟨t, by omega, by rw [show s + 2 + 2 * t = s + 2 * (t + 1) by ring]; exact h⟩

/-- A computable test for `IsPerimeter P`: `P = 2m` is even and some odd leg `s` with
`m / 2 < s < m` passes `legB m`. -/
def perimB (P : ℕ) : Bool := Nat.beq (P % 2) 0 && anyS (P / 2) (P / 8 + 2) (2 * (P / 8) + 1)

theorem perimB_iff (P : ℕ) : perimB P = true ↔ IsPerimeter P := by
  rw [isPerimeter_iff_legOK, perimB, Bool.and_eq_true, Nat.beq_eq, anyS_iff]
  constructor
  · rintro ⟨hP, t, -, hs⟩
    exact ⟨hP, _, (legB_iff _ _).1 hs⟩
  · rintro ⟨hP, s, hs⟩
    have := hs.1; have := hs.2.1; have := hs.2.2.1
    refine ⟨hP, (s - (2 * (P / 8) + 1)) / 2, by omega, ?_⟩
    rw [show 2 * (P / 8) + 1 + 2 * ((s - (2 * (P / 8) + 1)) / 2) = s by omega, legB_iff]
    exact hs

instance : DecidablePred IsPerimeter := fun P => decidable_of_iff _ (perimB_iff P)

/-! ### A096033: differences between a leg and the hypotenuse of a primitive Pythagorean
triangle -/

/-- `d` is the difference between a leg and the hypotenuse of a primitive Pythagorean triangle:
there are legs `x, y ≥ 1` with `gcd(x, y) = 1` and a hypotenuse `z` with `x² + y² = z²`, and
`z = x + d` (the legs play symmetric roles, so `x` is either leg). -/
def IsLegHypDiff (d : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ Nat.gcd x y = 1 ∧ z = x + d

/-- A096033 (offset `1`): the `n`-th smallest difference between a leg and the hypotenuse of a
primitive Pythagorean triangle. -/
noncomputable def A096033 (n : ℕ) : ℕ := Nat.nth IsLegHypDiff (n - 1)

/-- The differences are the odd squares and the numbers `2 j²`, `j ≥ 1` (as stated in the
entry A096033; proved here only to make `IsLegHypDiff` decidable). -/
theorem isLegHypDiff_iff (d : ℕ) : IsLegHypDiff d ↔
    (d % 2 = 1 ∧ ∃ k, k * k = d) ∨ (d % 2 = 0 ∧ 0 < d ∧ ∃ j, j * j = d / 2) := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hpy, hg, rfl⟩
    have h : PythagoreanTriple (x : ℤ) y ((x + d : ℕ) : ℤ) := by
      unfold PythagoreanTriple
      rw [← sq, ← sq, ← sq]
      exact_mod_cast hpy
    have hc : Int.gcd x y = 1 := by rw [Int.gcd_natCast_natCast]; exact hg
    have hzpos : (0 : ℤ) < ((x + d : ℕ) : ℤ) := by exact_mod_cast (show 0 < x + d by omega)
    rcases h.even_odd_of_coprime hc with ⟨-, hy2⟩ | ⟨hx2, -⟩
    · -- `x` even: `d = (m - n)²` with `m - n` odd
      have hc' : Int.gcd y x = 1 := by rw [Int.gcd_comm]; exact hc
      obtain ⟨m, n, -, hxe, hze, -, hpar, -⟩ := h.symm.coprime_classification' hc' hy2 hzpos
      have hd : (d : ℤ) = (m - n) * (m - n) := by
        have : ((x + d : ℕ) : ℤ) = x + d := by push_cast; ring
        rw [this] at hze
        linear_combination hze - hxe
      have hodd : (m - n) % 2 = 1 := by omega
      left
      refine ⟨?_, (m - n).natAbs, ?_⟩
      · obtain ⟨q, hq⟩ : ∃ q, m - n = 2 * q + 1 := ⟨(m - n) / 2, by omega⟩
        rw [hq] at hd
        have : (d : ℤ) = 2 * (2 * q * q + 2 * q) + 1 := by rw [hd]; ring
        generalize 2 * q * q + 2 * q = w at this
        omega
      · have := Int.natAbs_mul_self' (m - n)
        rw [← hd] at this
        exact_mod_cast this
    · -- `x` odd: `d = 2 n²` with `n ≠ 0`
      obtain ⟨m, n, hxe, hye, hze, -, -, -⟩ := h.coprime_classification' hc hx2 hzpos
      have e : ((n.natAbs * n.natAbs : ℕ) : ℤ) = n * n := by
        rw [Nat.cast_mul]
        exact Int.natAbs_mul_self' n
      have hd : (d : ℤ) = 2 * (n.natAbs * n.natAbs : ℕ) := by
        have : ((x + d : ℕ) : ℤ) = x + d := by push_cast; ring
        rw [this] at hze
        rw [e]
        linear_combination hze - hxe
      have hd' : d = 2 * (n.natAbs * n.natAbs) := by exact_mod_cast hd
      have hn : n ≠ 0 := by
        rintro rfl
        simp at hye
        omega
      have hpos : 0 < n.natAbs * n.natAbs := Nat.mul_pos (by omega) (by omega)
      right
      refine ⟨by omega, by omega, n.natAbs, by omega⟩
  · rintro (⟨hd, k, rfl⟩ | ⟨hd, hd0, j, hj⟩)
    · -- `d = k²`, `k = 2t+1`: the triangle `(2k+2, k²+2k, k²+2k+2)`
      obtain ⟨t, rfl⟩ : ∃ t, k = 2 * t + 1 := by
        refine ⟨k / 2, ?_⟩
        rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
        · exfalso
          have : (r + r) * (r + r) = 2 * (2 * r * r) := by ring
          omega
        · omega
      refine ⟨2 * (2 * t + 1) + 2, (2 * t + 1) * (2 * t + 1) + 2 * (2 * t + 1),
        (2 * t + 1) * (2 * t + 1) + 2 * (2 * t + 1) + 2, by omega, by positivity, by ring,
        ?_, by ring⟩
      apply Nat.isCoprime_iff_coprime.1
      exact ⟨(t + 1 : ℤ), -1, by push_cast; ring⟩
    · -- `d = 2 j²`: the triangle `(2j+1, 2j²+2j, 2j²+2j+1)`
      have hj0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with rfl | h
        · omega
        · exact h
      have hdj : d = 2 * (j * j) := by omega
      subst hdj
      refine ⟨2 * j + 1, 2 * (j * j) + 2 * j, 2 * (j * j) + 2 * j + 1, by omega, by positivity,
        by ring, ?_, by ring⟩
      apply Nat.isCoprime_iff_coprime.1
      exact ⟨(2 * j + 1 : ℤ), -2, by push_cast; ring⟩

/-- Boolean version of the characterization in `isLegHypDiff_iff`. -/
def legHypB (d : ℕ) : Bool :=
  (Nat.beq (d % 2) 1 && sqB d) || (Nat.beq (d % 2) 0 && Nat.blt 0 d && sqB (d / 2))

theorem legHypB_iff (d : ℕ) : legHypB d = true ↔ IsLegHypDiff d := by
  rw [isLegHypDiff_iff]
  simp [legHypB, sqB_iff, Nat.beq_eq, Nat.blt_eq, and_assoc]

instance : DecidablePred IsLegHypDiff := fun d => decidable_of_iff _ (legHypB_iff d)

/-! ### Data (kernel-checked) -/

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

/-- The perimeters `P` with `lo ≤ P < hi`, as found by the decision procedure. -/
def chunk (lo hi : ℕ) : List ℕ := (List.range' lo (hi - lo)).filter fun k => decide (IsPerimeter k)

theorem chunk_split {lo mid hi : ℕ} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    chunk lo hi = chunk lo mid ++ chunk mid hi := by
  unfold chunk
  rw [← List.filter_append, show hi - lo = (mid - lo) + (hi - mid) by omega,
    ← List.range'_append_1, show lo + (mid - lo) = mid by omega]

/-! The search below `3137` is split into chunks, each checked in the kernel separately (this
bounds the memory used by each kernel check). -/

theorem chunk_1 : chunk 0 1186 =
    [16, 18, 36, 50, 64, 98, 100, 144, 162, 196, 242, 256, 324, 338, 400, 450, 484, 576, 578, 676,
      722, 784, 882, 900, 1024, 1058, 1156] := by
  decide +kernel

theorem chunk_2 : chunk 1186 1677 =
    [1250, 1296, 1444, 1458, 1600] := by
  decide +kernel

theorem chunk_3 : chunk 1677 2054 =
    [1682, 1764, 1922, 1936] := by
  decide +kernel

theorem chunk_4 : chunk 2054 2371 =
    [2116, 2178, 2304] := by
  decide +kernel

theorem chunk_5 : chunk 2371 2651 =
    [2450, 2500] := by
  decide +kernel

theorem chunk_6 : chunk 2651 2904 =
    [2704, 2738] := by
  decide +kernel

theorem chunk_7 : chunk 2904 3137 =
    [2916, 3042, 3136] := by
  decide +kernel

/-- The perimeters below `3137` are the 46 listed terms. -/
theorem filter_range_3137 : (List.range 3137).filter (fun k => decide (IsPerimeter k)) =
    [16, 18, 36, 50, 64, 98, 100, 144, 162, 196, 242, 256, 324, 338, 400, 450, 484, 576, 578, 676,
      722, 784, 882, 900, 1024, 1058, 1156, 1250, 1296, 1444, 1458, 1600, 1682, 1764, 1922, 1936,
      2116, 2178, 2304, 2450, 2500, 2704, 2738, 2916, 3042, 3136] := by
  have h : (List.range 3137).filter (fun k => decide (IsPerimeter k)) = chunk 0 3137 := by
    rw [chunk, Nat.sub_zero, List.range_eq_range']
  rw [h,
    chunk_split (lo := 0) (mid := 1186) (hi := 3137) (by norm_num) (by norm_num),
    chunk_split (lo := 1186) (mid := 1677) (hi := 3137) (by norm_num) (by norm_num),
    chunk_split (lo := 1677) (mid := 2054) (hi := 3137) (by norm_num) (by norm_num),
    chunk_split (lo := 2054) (mid := 2371) (hi := 3137) (by norm_num) (by norm_num),
    chunk_split (lo := 2371) (mid := 2651) (hi := 3137) (by norm_num) (by norm_num),
    chunk_split (lo := 2651) (mid := 2904) (hi := 3137) (by norm_num) (by norm_num)]
  rw [chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7]
  rfl

/-- The definition reproduces all 46 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 46).map (fun i => a (i + 1)) =
    [16, 18, 36, 50, 64, 98, 100, 144, 162, 196, 242, 256, 324, 338, 400, 450, 484, 576, 578, 676,
      722, 784, 882, 900, 1024, 1058, 1156, 1250, 1296, 1444, 1458, 1600, 1682, 1764, 1922, 1936,
      2116, 2178, 2304, 2450, 2500, 2704, 2738, 2916, 3042, 3136] := by
  have : (fun i => a (i + 1)) = Nat.nth IsPerimeter := funext fun i => by simp [a]
  rw [this]
  exact map_nth_eq_of_filter filter_range_3137 rfl

/-- The definition of A096033 reproduces its 52 listed terms (kernel-checked). -/
theorem A096033_data : (List.range 52).map (fun i => A096033 (i + 1)) =
    [1, 2, 8, 9, 18, 25, 32, 49, 50, 72, 81, 98, 121, 128, 162, 169, 200, 225, 242, 288, 289,
      338, 361, 392, 441, 450, 512, 529, 578, 625, 648, 722, 729, 800, 841, 882, 961, 968,
      1058, 1089, 1152, 1225, 1250, 1352, 1369, 1458, 1521, 1568, 1681, 1682, 1800, 1849] := by
  have : (fun i => A096033 (i + 1)) = Nat.nth IsLegHypDiff := funext fun i => by simp [A096033]
  rw [this]
  exact map_nth_eq_of_filter (N := 1850) (by decide +kernel) rfl

/-! ### The conjecture -/

/-- Conjecture (Kagey, A308222): for every `n ≥ 1`, the `n`-th smallest perimeter of a primitive
Heronian isosceles triangle is twice the `(n + 2)`-th smallest difference between a leg and the
hypotenuse of a primitive Pythagorean triangle: `a(n) = 2 · A096033(n + 2)`. -/
def statement : Prop := ∀ n : ℕ, 1 ≤ n → a n = 2 * A096033 (n + 2)

end Math0.Statements.A308222
