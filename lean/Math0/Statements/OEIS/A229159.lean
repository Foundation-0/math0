/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A229159: smallest integer area of an integer triangle with a side of length prime(n)

Source: https://oeis.org/A229159, _Michel Lagneau_, Sep 17 2013. Verbatim:
> Conjecture: for all prime p > 2 there exists an integer-sided triangle with integer area where
> at least one side is of length p.

The entry's name: "Smallest integer areas of integer-sided triangles where at least one side is
of length prime(n)." Offset `1`, so `prime(1) = 2`. The listed `a(1) = 0` means that no such
triangle exists for `p = 2`.

## Encoding

* *Triangles.* An integer-sided triangle is a triple `x, y, z` of natural numbers satisfying the
  strict triangle inequalities `x < y + z`, `y < x + z`, `z < x + y`. These make the triangle
  non-degenerate and force `x, y, z ≥ 1`. Degenerate triangles are excluded. Otherwise every
  `p` would trivially have an area-`0` "triangle" `(p, p, 2p)`, and `a(1) = 0` would not mean
  "no triangle".
* *Integer area.* By Heron's formula, the area `S` of the triangle satisfies
  `16 S² = (x+y+z)(-x+y+z)(x-y+z)(x+y-z)`. "Integer area" means `S` is a natural number `A`,
  i.e. `16 A² = (x+y+z)(-x+y+z)(x-y+z)(x+y-z)` (computed in `ℤ`). This is `IsIntTriangle x y z A`.
  Under the strict triangle inequalities, `A > 0` automatically.
* *A side of length `p`.* `x = p ∨ y = p ∨ z = p`. `areas p` is the set of such integer areas.
* *The sequence.* `prime n = Nat.nth Nat.Prime (n - 1)` is the `n`-th prime (1-indexed), and
  `a n = sInf (areas (prime n))`. On `ℕ`, `sInf ∅ = 0`, which matches the OEIS convention
  `a(1) = 0`. The set `areas p` need not be finite or decidable a priori, so `a` is
  noncomputable. The values are certified by computable helpers:
  - a witness triangle `(p, b, c)` with Heron product `16 A₀²` (`entryOK`);
  - a kernel-checked search (`lbCheck`) showing that no triangle `(p, b, b + d)`, `0 ≤ d < p`,
    has an integer area `A < A₀`. For fixed `d` the Heron product is monotone in `b`, so each
    scan stops at the first `b` where the product reaches `16 A₀²` (`scan_spec`). Non-squares
    are certified by `r² < N < (r+1)²` for a Newton guess `r`.
  `a_one` proves `a 1 = 0` by hand: there is no integer triangle with integer area and a side of
  length `2`.
* *Data.* `a_data` checks the first 19 listed terms (`n = 1, …, 19`, primes up to `67`). The
  listed term `a(20) = 14910` (and also `a(25) = 420`, `a(29) = 840`, `a(32) = 11790`,
  `a(40) = 3276`) is **not** the minimum. The entry's Maple program only searches sides up to
  `500` and returns the first triangle found, not the smallest-area one. For example,
  `(71, 505, 560)` has area `11928` and `(97, 11, 90)` has area `396`. `oeis_errata` proves these
  upper bounds. The errata concern only the listed values, not the conjecture, which is a pure
  existence statement.
* *The conjecture.* `statement`: for every prime `p > 2` there are natural numbers `x, y, z, A`
  with `IsIntTriangle x y z A` and `p ∈ {x, y, z}`. Equivalently, `areas p` is nonempty, i.e.
  `a n ≠ 0` for every `n ≥ 2`.
-/

namespace Math0.Statements.A229159

/-- `x, y, z` are the side lengths of a non-degenerate triangle (strict triangle inequalities)
whose area is the natural number `A`. By Heron's formula,
`16 · area² = (x+y+z)(-x+y+z)(x-y+z)(x+y-z)`. -/
def IsIntTriangle (x y z A : ℕ) : Prop :=
  x < y + z ∧ y < x + z ∧ z < x + y ∧
    16 * (A : ℤ) ^ 2 =
      ((x : ℤ) + y + z) * (-(x : ℤ) + y + z) * ((x : ℤ) - y + z) * ((x : ℤ) + y - z)

/-- The integer areas of the integer-sided triangles having (at least) one side of length `m`. -/
def areas (m : ℕ) : Set ℕ :=
  {A | ∃ x y z : ℕ, IsIntTriangle x y z A ∧ (x = m ∨ y = m ∨ z = m)}

/-- The `n`-th prime, 1-indexed as in OEIS: `prime 1 = 2`, `prime 2 = 3`, … -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A229159: the smallest integer area of an integer-sided triangle having a side of length
`prime n`, and `0` if there is no such triangle (on `ℕ`, `sInf ∅ = 0`). Offset `1`. -/
noncomputable def a (n : ℕ) : ℕ := sInf (areas (prime n))

/-! ### Symmetry: we may assume the side `p` comes first and `b ≤ c` -/

theorem IsIntTriangle.swap12 {x y z A : ℕ} (h : IsIntTriangle x y z A) :
    IsIntTriangle y x z A := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [h4]; ring

theorem IsIntTriangle.swap13 {x y z A : ℕ} (h : IsIntTriangle x y z A) :
    IsIntTriangle z y x A := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [h4]; ring

theorem IsIntTriangle.swap23 {x y z A : ℕ} (h : IsIntTriangle x y z A) :
    IsIntTriangle x z y A := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [h4]; ring

theorem exists_le_of_isIntTriangle {m b c A : ℕ} (h : IsIntTriangle m b c A) :
    ∃ b c, b ≤ c ∧ IsIntTriangle m b c A := by
  rcases le_total b c with hbc | hbc
  · exact ⟨b, c, hbc, h⟩
  · exact ⟨c, b, hbc, h.swap23⟩

theorem mem_areas_iff (m A : ℕ) :
    A ∈ areas m ↔ ∃ b c, b ≤ c ∧ IsIntTriangle m b c A := by
  constructor
  · rintro ⟨x, y, z, h, rfl | rfl | rfl⟩
    · exact exists_le_of_isIntTriangle h
    · exact exists_le_of_isIntTriangle h.swap12
    · exact exists_le_of_isIntTriangle h.swap13
  · rintro ⟨b, c, -, h⟩
    exact ⟨m, b, c, h, Or.inl rfl⟩

/-! ### The Heron product in `ℕ` -/

/-- The Heron product `(p+b+c)(b+c-p)(p+c-b)(p+b-c)` in `ℕ` (truncated subtraction). It equals
the integer Heron product when the triangle inequalities hold. -/
def heronN (p b c : ℕ) : ℕ := (p + b + c) * (b + c - p) * (p + c - b) * (p + b - c)

theorem heronN_cast {p b c : ℕ} (h1 : p < b + c) (h2 : b < p + c) (h3 : c < p + b) :
    (heronN p b c : ℤ) =
      ((p : ℤ) + b + c) * (-(p : ℤ) + b + c) * ((p : ℤ) - b + c) * ((p : ℤ) + b - c) := by
  unfold heronN
  push_cast [Nat.cast_sub (show p ≤ b + c by omega), Nat.cast_sub (show b ≤ p + c by omega),
    Nat.cast_sub (show c ≤ p + b by omega)]
  ring

theorem isIntTriangle_iff_heronN (p b c A : ℕ) :
    IsIntTriangle p b c A ↔
      p < b + c ∧ b < p + c ∧ c < p + b ∧ heronN p b c = 16 * A ^ 2 := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rw [← heronN_cast h1 h2 h3] at h4
    exact_mod_cast h4.symm
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rw [← heronN_cast h1 h2 h3, h4]
    push_cast; ring

/-- For fixed `p` and `d`, the Heron product of `(p, b, b + d)` is monotone in `b`. -/
theorem heronN_mono {p d b b' : ℕ} (h : b ≤ b') :
    heronN p b (b + d) ≤ heronN p b' (b' + d) := by
  unfold heronN
  apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul _ _) _) _ <;> omega

/-! ### Certified search for the lower bound -/

/-- Newton iteration for the integer square root, with fuel. It is only a guess. Every use is
certified by `notSquareAux`. -/
def sqrtGuess : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | fuel + 1, N, g =>
    if (g + N / g) / 2 < g then sqrtGuess fuel N ((g + N / g) / 2) else g

/-- `r² < N < (r + 1)²`, which certifies that `N` is not a perfect square. -/
def notSquareAux (N r : ℕ) : Bool := r * r < N && N < (r + 1) * (r + 1)

/-- Certified non-square test (sound by `notSquare_spec`). -/
def notSquare (N : ℕ) : Bool := notSquareAux N (sqrtGuess 64 N (2 ^ (N.log2 / 2 + 1)))

theorem notSquare_spec {N : ℕ} (h : notSquare N = true) (A : ℕ) : A * A ≠ N := by
  simp only [notSquare, notSquareAux, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  set r := sqrtGuess 64 N (2 ^ (N.log2 / 2 + 1))
  intro hA
  rcases le_or_gt A r with hr | hr
  · have := Nat.mul_le_mul hr hr; omega
  · have h3 : r + 1 ≤ A := hr
    have := Nat.mul_le_mul h3 h3; omega

/-- The pair `(b, c)` (with Heron product `P`) is not a triangle, or `P ≠ 16 A²` for every `A`. -/
def pairOK (p b c P : ℕ) : Bool := !(p < b + c) || P % 16 != 0 || notSquare (P / 16)

/-- One step of `scan`: stop (successfully) once the Heron product `P` reaches `M`; otherwise
check the current pair and continue with `k`. -/
def scanAux (p M d b P : ℕ) (k : Bool) : Bool :=
  if M ≤ P then true else pairOK p b (b + d) P && k

/-- `scan p M d fuel b`: walk `b, b + 1, …` (at most `fuel` steps) through the triangles
`(p, b, b + d)` until the Heron product reaches `M`, checking that no Heron product below `M`
is `16 A²`. -/
def scan (p M d : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, b => scanAux p M d b (heronN p b (b + d)) (scan p M d fuel (b + 1))

theorem scan_spec (p M d : ℕ) :
    ∀ fuel b, scan p M d fuel b = true →
      ∀ b', b ≤ b' → ∀ A, IsIntTriangle p b' (b' + d) A → M ≤ 16 * A ^ 2 := by
  intro fuel
  induction fuel with
  | zero => intro b h; simp [scan] at h
  | succ fuel ih =>
    intro b h b' hb' A hA
    have hA' := (isIntTriangle_iff_heronN _ _ _ _).1 hA
    simp only [scan, scanAux] at h
    split_ifs at h with hM
    · rw [← hA'.2.2.2]
      exact hM.trans (heronN_mono hb')
    · rw [Bool.and_eq_true] at h
      rcases Nat.eq_or_lt_of_le hb' with rfl | hlt
      · exfalso
        have hP := h.1
        simp only [pairOK, hA'.2.2.2, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          not_lt, bne_iff_ne, ne_eq] at hP
        rcases hP with (hP | hP) | hP
        · exact absurd hA'.1 (not_lt.2 hP)
        · exact hP (by omega)
        · exact notSquare_spec (by rwa [show 16 * A ^ 2 / 16 = A * A by rw [sq]; omega] at hP) A rfl
      · exact ih (b + 1) h.2 b' hlt A hA

/-- No triangle `(p, b, c)` with `b ≤ c` has Heron product `16 A²` with `16 A² < M`
(see `lbCheck_spec`). -/
def lbCheck (p M : ℕ) : Bool := (List.range p).all fun d => scan p M d 100000 0

theorem lbCheck_spec {p M : ℕ} (h : lbCheck p M = true) {b c A : ℕ} (hbc : b ≤ c)
    (hA : IsIntTriangle p b c A) : M ≤ 16 * A ^ 2 := by
  have hd : c - b < p := by have := hA.2.2.1; omega
  have hs := List.all_eq_true.1 h (c - b) (List.mem_range.2 hd)
  refine scan_spec p M (c - b) 100000 0 hs b (Nat.zero_le b) A ?_
  rwa [show b + (c - b) = c by omega]

/-! ### Certified values -/

/-- Check that `p` is the `n`-th prime and that `(p, b, c)` is a triangle with Heron product
`16 A²`, so that `A ∈ areas (prime n)` (`witnessOK_spec`). -/
def witnessOK (n p A b c : ℕ) : Bool :=
  decide (Nat.Prime p) && Nat.count Nat.Prime p == n - 1 &&
    decide (p < b + c) && decide (b < p + c) && decide (c < p + b) &&
    heronN p b c == 16 * A ^ 2

/-- `witnessOK`, and no triangle with a side `p` has an integer area below `A₀`, so that
`a n = A₀` (`a_eq_of_entryOK`). -/
def entryOK (n p A₀ b c : ℕ) : Bool :=
  witnessOK n p A₀ b c && lbCheck p (16 * A₀ ^ 2)

theorem prime_eq {n p : ℕ} (hp : Nat.Prime p) (hc : Nat.count Nat.Prime p = n - 1) :
    prime n = p := by
  rw [prime, ← hc]
  exact Nat.nth_count hp

theorem witnessOK_spec {n p A b c : ℕ} (h : witnessOK n p A b c = true) :
    prime n = p ∧ A ∈ areas p := by
  simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hp, hc⟩, h1⟩, h2⟩, h3⟩, hH⟩ := h
  exact ⟨prime_eq hp hc, p, b, c, (isIntTriangle_iff_heronN p b c A).2 ⟨h1, h2, h3, hH⟩,
    Or.inl rfl⟩

theorem a_le_of_witnessOK {n p A b c : ℕ} (h : witnessOK n p A b c = true) : a n ≤ A := by
  obtain ⟨hp, hA⟩ := witnessOK_spec h
  rw [a, hp]
  exact Nat.sInf_le hA

theorem a_eq_of_entryOK {n p A₀ b c : ℕ} (h : entryOK n p A₀ b c = true) : a n = A₀ := by
  rw [entryOK, Bool.and_eq_true] at h
  obtain ⟨hp, hA₀⟩ := witnessOK_spec h.1
  rw [a, hp]
  refine IsLeast.csInf_eq ⟨hA₀, ?_⟩
  intro A hA
  obtain ⟨b', c', hle, ht⟩ := (mem_areas_iff _ _).1 hA
  have := lbCheck_spec h.2 hle ht
  by_contra hlt
  replace hlt := not_le.1 hlt
  have : A ^ 2 < A₀ ^ 2 := Nat.pow_lt_pow_left hlt two_ne_zero
  omega

/-- `a 1 = 0`: there is no integer-sided triangle with integer area and a side of length
`prime 1 = 2`. With sides `2 ≤ b ≤ c < b + 2`, either `c = b` and `A² = b² - 1`, which is not a
square, or `c = b + 1` and `16 A² = 3 (2b + 3)(2b - 1)`, which is odd. -/
theorem areas_two : areas 2 = ∅ := by
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA
  obtain ⟨b, c, hbc, h1, h2, h3, h4⟩ := (mem_areas_iff 2 A).1 hA
  push_cast at h4
  rcases (show c = b ∨ c = b + 1 by omega) with hc | hc
  · subst c
    have hb : (2 : ℤ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
    have h16 : (16 : ℤ) * (A : ℤ) ^ 2 = 16 * ((b : ℤ) ^ 2 - 1) := by linear_combination h4
    have key : (A : ℤ) ^ 2 = (b : ℤ) ^ 2 - 1 := mul_left_cancel₀ (by norm_num) h16
    have hA0 : (0 : ℤ) ≤ A := by positivity
    rcases le_or_gt (A : ℤ) (b - 1) with h | h
    · nlinarith [mul_le_mul h h hA0 (by linarith)]
    · have h' : (b : ℤ) ≤ A := by linarith
      nlinarith [mul_le_mul h' h' (by linarith) hA0]
  · subst c
    push_cast at h4
    have key : (16 : ℤ) * (A : ℤ) ^ 2 = 12 * (b : ℤ) ^ 2 + 12 * b - 9 := by
      linear_combination h4
    generalize (A : ℤ) ^ 2 = X at key
    generalize (b : ℤ) ^ 2 = Y at key
    omega

theorem a_one : a 1 = 0 := by
  rw [a, prime, Nat.sub_self, Nat.nth_prime_zero_eq_two, areas_two, Nat.sInf_empty]

/-- `(n, prime n, a n, b, c)` for `n = 2, …, 19`, where `(prime n, b, c)` is a triangle of
area `a n` (the same triangles as in the entry's table). -/
def table : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(2, 3, 6, 4, 5), (3, 5, 6, 3, 4), (4, 7, 42, 15, 20), (5, 11, 66, 13, 20), (6, 13, 24, 4, 15),
    (7, 17, 36, 9, 10), (8, 19, 114, 20, 37), (9, 23, 966, 140, 159), (10, 29, 60, 6, 25),
    (11, 31, 930, 68, 87), (12, 37, 114, 19, 20), (13, 41, 126, 15, 28), (14, 43, 1290, 61, 68),
    (15, 47, 4230, 425, 468), (16, 53, 90, 4, 51), (17, 59, 1770, 68, 109),
    (18, 61, 330, 11, 60), (19, 67, 2814, 85, 116)]

/-- Kernel check of every entry of `table` (primality, prime index, witness, lower bound). -/
theorem table_ok :
    table.all (fun e => entryOK e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2) = true := by
  decide +kernel

theorem a_table : ∀ e ∈ table, a e.1 = e.2.2.1 := fun e he =>
  a_eq_of_entryOK (List.all_eq_true.1 table_ok e he)

/-- The definition reproduces the first 19 terms listed in OEIS (`n = 1, …, 19`), kernel-checked
through `table_ok` (`a 1 = 0` by `a_one`). -/
theorem a_data : (List.range 19).map (fun i => a (i + 1)) =
    [0, 6, 6, 42, 66, 24, 36, 114, 966, 60, 930, 114, 126, 1290, 4230, 90, 1770, 330, 2814] := by
  have hidx : table.map (fun e => e.1) = (List.range 18).map (fun i => i + 2) := by
    decide +kernel
  calc (List.range 19).map (fun i => a (i + 1))
      = a 1 :: ((List.range 18).map (fun i => i + 2)).map a := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.map_map]; rfl
    _ = a 1 :: table.map (fun e => a e.1) := by rw [← hidx, List.map_map]; rfl
    _ = 0 :: table.map (fun e => e.2.2.1) := by rw [a_one, List.map_congr_left a_table]
    _ = _ := by decide +kernel

/-- Errata: some listed terms are not minimal. The triangles `(71, 505, 560)`, `(97, 11, 90)`,
`(109, 11, 100)`, `(131, 265, 390)` and `(173, 36, 187)` have integer areas `11928 < 14910`,
`396 < 420`, `330 < 840`, `6288 < 11790` and `2970 < 3276` (the listed `a(20)`, `a(25)`, `a(29)`,
`a(32)`, `a(40)`). -/
theorem oeis_errata : a 20 ≤ 11928 ∧ a 25 ≤ 396 ∧ a 29 ≤ 330 ∧ a 32 ≤ 6288 ∧ a 40 ≤ 2970 :=
  ⟨a_le_of_witnessOK (p := 71) (b := 505) (c := 560) (by decide +kernel),
    a_le_of_witnessOK (p := 97) (b := 11) (c := 90) (by decide +kernel),
    a_le_of_witnessOK (p := 109) (b := 11) (c := 100) (by decide +kernel),
    a_le_of_witnessOK (p := 131) (b := 265) (c := 390) (by decide +kernel),
    a_le_of_witnessOK (p := 173) (b := 36) (c := 187) (by decide +kernel)⟩

/-! ### The conjecture -/

/-- Conjecture (Lagneau, A229159): for every prime `p > 2` there is an integer-sided
(non-degenerate) triangle with integer area having at least one side of length `p`. -/
def statement : Prop :=
  ∀ p : ℕ, p.Prime → 2 < p →
    ∃ x y z A : ℕ, IsIntTriangle x y z A ∧ (x = p ∨ y = p ∨ z = p)

end Math0.Statements.A229159
