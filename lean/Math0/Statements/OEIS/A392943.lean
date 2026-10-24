/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A392943: triangles with integer sides, area and circumradius, by semiperimeter

Source: https://oeis.org/A392943, _Felix Huber_, Feb 04 2026. Verbatim:
> Conjecture: There is no primitive Heronian triangle with integer circumradius.

The entry's name: "a(n) is the number of integer-sided triangles whose area and circumradius are
integers, and whose semiperimeter equals A392942(n)." (offset `1`). A392942 (same author, offset
`1`) is "Distinct semiperimeters of triangles with integer sides, integer area, and integer
circumradius.", listed in increasing order.

## Encoding

* A triangle is a triple of positive integer side lengths `x, y, z` satisfying the strict
  triangle inequalities (`IsTriangle`), so it is nondegenerate.
* Area: by Heron's formula `16 · area² = (x+y+z)(-x+y+z)(x-y+z)(x+y-z)` (`heron16`). "Integer
  area" means the area is a natural number `K`, i.e. `16 K² = heron16 x y z` (`HasArea`); for a
  triangle the area is positive, so `K > 0`.
* Circumradius: `R = x y z / (4 K)`. Since `K > 0`, "integer circumradius" means
  `4 K R = x y z` for a natural number `R` (the circumradius is positive).
* A Heronian triangle is one with integer sides and integer area; it is primitive when
  `gcd(x, y, z) = 1`. `statement` says: no triangle with integer sides `x, y, z`,
  `gcd(x, y, z) = 1` and integer area `K` has integer circumradius.
* For the sequence, triangles are counted up to congruence, i.e. as `x ≤ y ≤ z` (as in the
  entry's Maple program and examples). The semiperimeter is `(x + y + z) / 2`, so "semiperimeter
  `s`" means `x + y + z = 2 s`. No triangle is lost by taking `s` to be a natural number: a
  triangle with integer sides and integer area has even perimeter (`even_perimeter`). `count s`
  is computed by a fast loop and `count_eq_card` proves that it is the number of such triples
  `(x, y, z)` (the Finset `triangles s`).
* `A392942 n` is computed by a search over `s ≤ 12 n` (every positive multiple of `12` is a
  semiperimeter, by `isSemiperimeter_twelve_mul`), and `A392942_eq_nth` proves that it is the
  `n`-th smallest semiperimeter, `Nat.nth IsSemiperimeter (n - 1)`, for `n ≥ 1`.
  `a n = count (A392942 n)`; the value `a 0` is a junk value outside the OEIS offset.
* `a_data` checks the first 30 of the 88 listed terms (semiperimeters up to `A392942 30 = 156`);
  all 88 listed terms agree with this definition in an independent Python computation.
-/

namespace Math0.Statements.A392943

/-- `x, y, z` are the side lengths of a nondegenerate triangle. -/
def IsTriangle (x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ x < y + z ∧ y < x + z ∧ z < x + y

/-- Heron's formula: `16 · area² = (x+y+z)(-x+y+z)(x-y+z)(x+y-z)`. -/
def heron16 (x y z : ℕ) : ℤ :=
  ((x : ℤ) + y + z) * (-x + y + z) * (x - y + z) * (x + y - z)

/-- The triangle with sides `x, y, z` has area `K`, i.e. `16 K² = heron16 x y z`. -/
def HasArea (x y z K : ℕ) : Prop :=
  16 * (K : ℤ) ^ 2 = heron16 x y z

/-- `x, y, z` is a triangle with integer sides, integer area `K` and integer circumradius
`R = x y z / (4 K)`. -/
def IsGood (x y z : ℕ) : Prop :=
  IsTriangle x y z ∧ ∃ K R : ℕ, HasArea x y z K ∧ 4 * K * R = x * y * z

/-! ### A fast Boolean decision procedure for `IsGood` (`goodB_iff`)

The kernel evaluates the raw functions `Nat.add`, `Nat.ble`, ... much faster than the
corresponding notation, so the Boolean functions below are written with them. -/

/-- Boolean version of `IsTriangle`. -/
def triB (x y z : ℕ) : Bool :=
  Nat.blt 0 x && Nat.blt 0 y && Nat.blt 0 z && Nat.blt x (Nat.add y z) &&
    Nat.blt y (Nat.add x z) && Nat.blt z (Nat.add x y)

theorem triB_iff (x y z : ℕ) : triB x y z = true ↔ IsTriangle x y z := by
  simp [triB, IsTriangle, Nat.blt_eq, and_assoc]

/-- `sqMaskAux m n`: the bitmask with bit `r * r % m` set for every `r < n`. -/
def sqMaskAux (m n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun r acc => Nat.lor acc (Nat.shiftLeft 1 (Nat.mod (Nat.mul r r) m))) n

/-- The bitmask of the squares modulo `m`. -/
def sqMask (m : ℕ) : ℕ := sqMaskAux m m

theorem testBit_sqMaskAux (m n t : ℕ) (ht : t < n) :
    (sqMaskAux m n).testBit (t * t % m) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    show ((sqMaskAux m n) ||| (1 <<< (n * n % m))).testBit (t * t % m) = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | rfl
    · exact Or.inl (ih h)
    · right; simp [Nat.testBit_shiftLeft]

/-- Bit number `n % m` of the bitmask of the squares modulo `m`: a necessary condition for `n`
to be a perfect square (`qrBit_mul_self`). -/
def qrBit (m n : ℕ) : Bool :=
  Nat.beq (Nat.mod (Nat.shiftRight (sqMask m) (Nat.mod n m)) 2) 1

theorem qrBit_eq_testBit (m n : ℕ) : qrBit m n = (sqMask m).testBit (n % m) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff]
  show Nat.beq ((sqMask m >>> (n % m)) % 2) 1 = true ↔ _
  rw [Nat.shiftRight_eq_div_pow, Nat.beq_eq, decide_eq_true_eq]

theorem qrBit_mul_self (m r : ℕ) (hm : 0 < m) : qrBit m (r * r) = true := by
  rw [qrBit_eq_testBit, Nat.mul_mod]
  exact testBit_sqMaskAux m m _ (Nat.mod_lt _ hm)

/-- A quick sieve: `false` only if `n` is not a perfect square, using the squares modulo
`4095 = 63 · 65`, `3553 = 11 · 17 · 19`, `667 = 23 · 29`, `1147 = 31 · 37`, `1763 = 41 · 43`
(see `maybeSquare_mul_self`). -/
def maybeSquare (n : ℕ) : Bool :=
  qrBit 4095 n && (qrBit 3553 n && (qrBit 667 n && (qrBit 1147 n && qrBit 1763 n)))

theorem maybeSquare_mul_self (r : ℕ) : maybeSquare (r * r) = true := by
  simp [maybeSquare, qrBit_mul_self]

/-- `16 · area²` computed in `ℕ` (exact for triangles, where no subtraction truncates). -/
def heronNat (x y z : ℕ) : ℕ :=
  Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.add x y) z) (Nat.sub (Nat.add y z) x))
    (Nat.sub (Nat.add x z) y)) (Nat.sub (Nat.add x y) z)

theorem heron16_eq (x y z : ℕ) (h : IsTriangle x y z) :
    heron16 x y z = (heronNat x y z : ℤ) := by
  obtain ⟨-, -, -, h1, h2, h3⟩ := h
  have e : heronNat x y z = (x + y + z) * (y + z - x) * (x + z - y) * (x + y - z) := rfl
  rw [heron16, e]
  push_cast [Nat.cast_sub h1.le, Nat.cast_sub h2.le, Nat.cast_sub h3.le]
  ring

/-- With `r = ⌊√P⌋`, `P = heronNat x y z`: `P = r²`, `4 ∣ r` (so the area is `K = r / 4`) and
`r = 4 K` divides `x y z`. -/
def finishB (x y z r : ℕ) : Bool :=
  Nat.beq (Nat.mul r r) (heronNat x y z) &&
    (Nat.beq (Nat.mod r 4) 0 && Nat.beq (Nat.mod (Nat.mul (Nat.mul x y) z) r) 0)

theorem finishB_eq (x y z r : ℕ) : finishB x y z r =
    (Nat.beq (r * r) (heronNat x y z) && (Nat.beq (r % 4) 0 && Nat.beq (x * y * z % r) 0)) :=
  rfl

/-- `IsGood x y z` for a triangle `x, y, z`: the sieve, then the exact test on `⌊√P⌋`. -/
def coreB (x y z : ℕ) : Bool :=
  maybeSquare (heronNat x y z) && finishB x y z (Nat.sqrt (heronNat x y z))

/-- Boolean version of `IsGood`, see `goodB_iff`. -/
def goodB (x y z : ℕ) : Bool :=
  triB x y z && coreB x y z

theorem goodB_iff (x y z : ℕ) : goodB x y z = true ↔ IsGood x y z := by
  constructor
  · intro h
    simp only [goodB, coreB, finishB_eq, Bool.and_eq_true, Nat.beq_eq, triB_iff] at h
    obtain ⟨htri, -, hsq, h4, hdvd⟩ := h
    set r := Nat.sqrt (heronNat x y z)
    obtain ⟨K, hK⟩ := Nat.dvd_of_mod_eq_zero h4
    refine ⟨htri, K, x * y * z / r, ?_, ?_⟩
    · rw [HasArea, heron16_eq _ _ _ htri, ← hsq, hK]
      push_cast; ring
    · rw [← hK, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdvd)]
  · rintro ⟨htri, K, R, hK, hR⟩
    have hP : heronNat x y z = (4 * K) * (4 * K) := by
      rw [HasArea, heron16_eq _ _ _ htri] at hK
      have : ((heronNat x y z : ℕ) : ℤ) = (((4 * K) * (4 * K) : ℕ) : ℤ) := by
        rw [← hK]; push_cast; ring
      exact_mod_cast this
    simp only [goodB, coreB, finishB_eq, Bool.and_eq_true, Nat.beq_eq, triB_iff, hP, Nat.sqrt_eq,
      maybeSquare_mul_self]
    refine ⟨htri, trivial, trivial, by simp, ?_⟩
    rw [← hR]; simp [Nat.mul_mod_right]

instance (x y z : ℕ) : Decidable (IsGood x y z) := decidable_of_iff _ (goodB_iff x y z)

/-- A triangle with integer sides and integer area has even perimeter: otherwise all four
factors of `heron16` are odd, while `16 K²` is even. -/
theorem even_perimeter {x y z : ℕ} (h : IsGood x y z) : Even (x + y + z) := by
  obtain ⟨-, K, -, hK, -⟩ := h
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h1 : Odd ((x : ℤ) + y + z) := by
    have := (Int.odd_coe_nat (x + y + z)).2 hodd
    push_cast at this
    exact this
  have h2 : Odd (-(x : ℤ) + y + z) := by
    have e : -(x : ℤ) + y + z = ((x : ℤ) + y + z) - 2 * x := by ring
    rw [e]; exact h1.sub_even (even_two_mul _)
  have h3 : Odd ((x : ℤ) - y + z) := by
    have e : (x : ℤ) - y + z = ((x : ℤ) + y + z) - 2 * y := by ring
    rw [e]; exact h1.sub_even (even_two_mul _)
  have h4 : Odd ((x : ℤ) + y - z) := by
    have e : (x : ℤ) + y - z = ((x : ℤ) + y + z) - 2 * z := by ring
    rw [e]; exact h1.sub_even (even_two_mul _)
  have hodd16 : Odd (heron16 x y z) := ((h1.mul h2).mul h3).mul h4
  rw [HasArea] at hK
  rw [← hK] at hodd16
  exact (Int.not_even_iff_odd.2 hodd16) ⟨8 * (K : ℤ) ^ 2, by ring⟩

/-! ### Counting the triangles with a given semiperimeter -/

/-- `sumIco a b f = ∑ k ∈ [a, b), f k`, written with the recursor so that the kernel
evaluates it quickly (see `sumIco_eq`). -/
def sumIco (a b : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.add acc (f (Nat.add a k))) (b - a)

theorem sumIco_eq (a b : ℕ) (f : ℕ → ℕ) : sumIco a b f = ∑ k ∈ Finset.Ico a b, f k := by
  rw [Finset.sum_Ico_eq_sum_range]
  unfold sumIco
  induction b - a with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- The triangle with sides `x ≤ y ≤ z = 2 s - x - y` is counted (Boolean form, `condB_iff`). -/
def condB (s x y : ℕ) : Bool :=
  Nat.ble (Nat.add x y) (Nat.mul 2 s) && Nat.ble x y &&
    Nat.ble y (Nat.sub (Nat.sub (Nat.mul 2 s) x) y) &&
    goodB x y (Nat.sub (Nat.sub (Nat.mul 2 s) x) y)

theorem condB_iff (s x y : ℕ) : condB s x y = true ↔
    x + y ≤ 2 * s ∧ x ≤ y ∧ y ≤ 2 * s - x - y ∧ IsGood x y (2 * s - x - y) := by
  simp only [condB, Bool.and_eq_true, Nat.ble_eq, goodB_iff, and_assoc]
  rfl

/-- Number of triangles with integer sides `x ≤ y ≤ z`, semiperimeter `s` (`x + y + z = 2 s`),
integer area and integer circumradius. The loops run over `1 ≤ x ≤ 2 s / 3` and
`max(x, s + 1 - x) ≤ y ≤ (2 s - x) / 2`, i.e. exactly over the triangles `x ≤ y ≤ z = 2 s - x - y`
(`condB_eq_coreB`), so only the area and circumradius test `coreB` is needed in the loop body.
`count_eq_card` proves that this counts the triangles in question. -/
def count (s : ℕ) : ℕ :=
  sumIco 1 (2 * s / 3 + 1) fun x =>
    sumIco (max x (s + 1 - x)) ((2 * s - x) / 2 + 1) fun y =>
      (coreB x y (Nat.sub (Nat.sub (Nat.mul 2 s) x) y)).toNat

/-- The triangles counted by `count s`: triples `(x, y, z)` with `x ≤ y ≤ z`, `x + y + z = 2 s`,
integer area and integer circumradius. -/
def triangles (s : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (2 * s + 1) ×ˢ Finset.range (2 * s + 1) ×ˢ Finset.range (2 * s + 1)).filter
    fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = 2 * s ∧ IsGood t.1 t.2.1 t.2.2

theorem condB_eq_coreB {s x y : ℕ} (hx : x ∈ Finset.Ico 1 (2 * s / 3 + 1))
    (hy : y ∈ Finset.Ico (max x (s + 1 - x)) ((2 * s - x) / 2 + 1)) :
    condB s x y = coreB x y (Nat.sub (Nat.sub (Nat.mul 2 s) x) y) := by
  simp only [Finset.mem_Ico, max_le_iff] at hx hy
  have e : Nat.sub (Nat.sub (Nat.mul 2 s) x) y = 2 * s - x - y := rfl
  have h1 : Nat.ble (Nat.add x y) (Nat.mul 2 s) = true := by
    rw [Nat.ble_eq]; show x + y ≤ 2 * s; omega
  have h2 : Nat.ble x y = true := by rw [Nat.ble_eq]; omega
  have h3 : Nat.ble y (Nat.sub (Nat.sub (Nat.mul 2 s) x) y) = true := by
    rw [Nat.ble_eq, e]; omega
  have h4 : triB x y (Nat.sub (Nat.sub (Nat.mul 2 s) x) y) = true :=
    (triB_iff _ _ _).2 (by rw [e]; unfold IsTriangle; omega)
  simp only [condB, goodB, h1, h2, h3, h4, Bool.true_and]

theorem condB_bounds {s x y : ℕ} (h : condB s x y = true) :
    x ∈ Finset.Ico 1 (2 * s / 3 + 1) ∧
      y ∈ Finset.Ico (max x (s + 1 - x)) ((2 * s - x) / 2 + 1) := by
  rw [condB_iff] at h
  obtain ⟨h1, h2, h3, ⟨hx, hy, hz, t1, t2, t3⟩, -⟩ := h
  simp only [Finset.mem_Ico, max_le_iff]
  omega

theorem sum_z (s x y : ℕ) :
    ∑ z ∈ Finset.range (2 * s + 1),
      (if x ≤ y ∧ y ≤ z ∧ x + y + z = 2 * s ∧ IsGood x y z then 1 else 0) =
    (condB s x y).toNat := by
  rw [Finset.sum_eq_single (2 * s - x - y)]
  · by_cases hxy : x + y ≤ 2 * s
    · have e : x + y + (2 * s - x - y) = 2 * s := by omega
      by_cases hc : condB s x y = true
      · rw [hc, if_pos]
        · rfl
        rw [condB_iff] at hc
        exact ⟨hc.2.1, hc.2.2.1, e, hc.2.2.2⟩
      · rw [Bool.not_eq_true] at hc
        rw [hc, if_neg]
        · rfl
        rintro ⟨h1, h2, -, h4⟩
        have := (condB_iff s x y).2 ⟨hxy, h1, h2, h4⟩
        rw [hc] at this
        exact absurd this (by decide)
    · have hc : condB s x y = false := by
        rw [← Bool.not_eq_true, condB_iff]; omega
      rw [hc, if_neg]
      · rfl
      omega
  · intro z _ hz
    rw [if_neg]
    omega
  · intro h; simp at h; omega

/-- `count s` is the number of triangles with integer sides, area and circumradius and
semiperimeter `s`, up to congruence. -/
theorem count_eq_card (s : ℕ) : count s = (triangles s).card := by
  rw [triangles, Finset.card_filter, Finset.sum_product]
  simp_rw [Finset.sum_product, sum_z]
  rw [count, sumIco_eq]
  have hR : ∀ x : ℕ, x ∈ Finset.Ico 1 (2 * s / 3 + 1) →
      sumIco (max x (s + 1 - x)) ((2 * s - x) / 2 + 1)
          (fun y => (coreB x y (Nat.sub (Nat.sub (Nat.mul 2 s) x) y)).toNat) =
        ∑ y ∈ Finset.range (2 * s + 1), (condB s x y).toNat := by
    intro x hx
    rw [sumIco_eq, ← Finset.sum_congr rfl fun y hy => congrArg Bool.toNat (condB_eq_coreB hx hy)]
    apply Finset.sum_subset
    · intro y hy; simp only [Finset.mem_Ico, Finset.mem_range] at hy ⊢; omega
    · intro y _ hy
      cases hc : condB s x y
      · rfl
      · exact absurd (condB_bounds hc).2 hy
  rw [Finset.sum_congr rfl hR]
  apply Finset.sum_subset
  · intro x hx; simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢; omega
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro y _
    cases hc : condB s x y
    · rfl
    · exact absurd (condB_bounds hc).1 hx

/-! ### The semiperimeters (OEIS A392942) -/

/-- `s` is the semiperimeter of some triangle with integer sides, integer area and integer
circumradius. -/
def IsSemiperimeter (s : ℕ) : Prop := 0 < count s

instance : DecidablePred IsSemiperimeter := fun s => inferInstanceAs (Decidable (0 < count s))

theorem isGood_scaled (m : ℕ) (hm : 0 < m) : IsGood (6 * m) (8 * m) (10 * m) := by
  refine ⟨by unfold IsTriangle; omega, 24 * m ^ 2, 5 * m, ?_, by ring⟩
  simp only [HasArea, heron16]
  push_cast
  ring

/-- Every positive multiple of `12` is a semiperimeter: the triangle `(6m, 8m, 10m)` has
semiperimeter `12 m`, area `24 m²` and circumradius `5 m`. -/
theorem isSemiperimeter_twelve_mul (m : ℕ) (hm : 0 < m) : IsSemiperimeter (12 * m) := by
  rw [IsSemiperimeter, count_eq_card, Finset.card_pos]
  refine ⟨(6 * m, 8 * m, 10 * m), ?_⟩
  simp only [triangles, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨by omega, by omega, by omega⟩, by omega, by omega, by omega, isGood_scaled m hm⟩

theorem le_count_twelve_mul (n : ℕ) : n ≤ Nat.count IsSemiperimeter (12 * n + 1) := by
  rw [Nat.count_eq_card_filter_range]
  calc n = ((Finset.range n).image fun k => 12 * (k + 1)).card := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]
    _ ≤ _ := by
        apply Finset.card_le_card
        intro t ht
        simp only [Finset.mem_image, Finset.mem_range] at ht
        obtain ⟨k, hk, rfl⟩ := ht
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, isSemiperimeter_twelve_mul _ (by omega)⟩

theorem infinite_isSemiperimeter : (Set.ofPred IsSemiperimeter).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have := hB (show 12 * (B + 1) ∈ Set.ofPred IsSemiperimeter from
    isSemiperimeter_twelve_mul _ (by omega))
  omega

/-- OEIS A392942 (`n ≥ 1`): the `n`-th smallest semiperimeter, found as the `s ≤ 12 n` that is
a semiperimeter with exactly `n - 1` semiperimeters below it (see `A392942_eq_nth`). -/
def A392942 (n : ℕ) : ℕ :=
  ((List.range (12 * n + 1)).find? fun s =>
    IsSemiperimeter s ∧ Nat.count IsSemiperimeter s = n - 1).getD 0

theorem A392942_eq_nth (n : ℕ) (hn : 1 ≤ n) :
    A392942 n = Nat.nth IsSemiperimeter (n - 1) := by
  set m := Nat.nth IsSemiperimeter (n - 1)
  have hpm : IsSemiperimeter m := Nat.nth_mem_of_infinite infinite_isSemiperimeter _
  have hcm : Nat.count IsSemiperimeter m = n - 1 :=
    Nat.count_nth_of_infinite infinite_isSemiperimeter _
  have hmlt : m < 12 * n + 1 :=
    Nat.nth_lt_of_lt_count (by have := le_count_twelve_mul n; omega)
  unfold A392942
  cases hf : (List.range (12 * n + 1)).find? fun s =>
      IsSemiperimeter s ∧ Nat.count IsSemiperimeter s = n - 1 with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp [hpm, hcm]) (hf m (List.mem_range.2 hmlt))
  | some t =>
    have ht := List.find?_some hf
    simp only [decide_eq_true_eq] at ht
    exact Nat.count_injective ht.1 hpm (ht.2.trans hcm.symm)

/-! ### The sequence -/

/-- OEIS A392943: `a n` is the number of triangles with integer sides, integer area and integer
circumradius whose semiperimeter is `A392942 n` (counted up to congruence, see
`count_eq_card`). -/
def a (n : ℕ) : ℕ := count (A392942 n)

/-- The definition reproduces the first terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 30).map (fun i => a (i + 1)) =
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 3, 1, 2,
      2] := by
  decide +kernel

/-- There is no primitive Heronian triangle with integer circumradius: for every triangle with
integer sides `x, y, z` with `gcd(x, y, z) = 1` and integer area `K`, the circumradius
`x y z / (4 K)` is not an integer `R`. -/
def statement : Prop :=
  ∀ x y z K R : ℕ, IsTriangle x y z → HasArea x y z K → Nat.gcd x (Nat.gcd y z) = 1 →
    4 * K * R ≠ x * y * z

end Math0.Statements.A392943
