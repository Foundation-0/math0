/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A354571: even legs of primitive Pythagorean triangles with odd prime factors `≡ 3 (mod 4)`

Source: https://oeis.org/A354571, _Lothar Selle_, Jun 04 2022 (COMMENTS section). Verbatim:
> Conjecture: lim_{n->oo} a(n)/n = Pi. Also, lim_{n->oo} A354570(n)/n = Pi.

A354571 (offset `1`) is "Ordered even leg lengths k (listed with multiplicity) of primitive
Pythagorean triangles such that all odd prime factors of k are congruent to 3 (mod 4) and at
least one prime factor is odd." (`12, 12, 24, 24, 28, 28, 36, …`; `12` is listed twice because of
the triangles `(5,12,13)` and `(12,35,37)`.)

A354570 (offset `1`, same author, Jun 03 2022) is "Ordered odd leg lengths k (listed with
multiplicity) of primitive Pythagorean triangles such that all prime factors of k are congruent
to 3 (mod 4)." (`3, 7, 9, 11, 19, 21, 21, 23, …`.) The conjecture speaks about both sequences, so
both are formalized here.

## Encoding

* `IsPPT x y z`: `(x, y, z)` is a primitive Pythagorean triangle with legs `x, y` and hypotenuse
  `z`, i.e. `0 < x`, `0 < y`, `x² + y² = z²` and `gcd(x, y, z) = 1`.
* `legTriangles k : Finset (ℕ × ℕ)` is the set of pairs `(b, c)` (other leg, hypotenuse) such
  that `IsPPT b k c`, i.e. it lists the primitive Pythagorean triangles having `k` as a leg, each
  exactly once (a triangle cannot have two equal legs, since `2x² = z²` has no positive integer
  solution). The theorem `mem_legTriangles` proves `(b, c) ∈ legTriangles k ↔ IsPPT b k c` for all
  `k, b, c`; the `Finset` is computed by running `d = c - b` over `0, …, k - 1` (if `b² + k² = c²`
  with `b, k > 0`, then `k² = d (2b + d)`, so `d < k`, `b = (k²/d - d)/2` and `c = b + d`), which
  only matters for the speed of evaluation.
* The multiplicity of `k` in A354571 is the number of primitive Pythagorean triangles whose even
  leg is `k`: `wE k = #legTriangles k` if `k` is even and satisfies `CondE k`, else `0`. Here
  `CondE k` says that every odd prime factor `p` of `k` (`p ∈ k.primeFactors`, `Odd p`) satisfies
  `p % 4 = 3`, and some prime factor of `k` is odd. Likewise the multiplicity of `k` in A354570 is
  `wO k = #legTriangles k` if `k` is odd and satisfies `CondO k` (every prime factor of `k` is
  `≡ 3 (mod 4)`), else `0`.
* For a weight `w`, `numLE w k = ∑_{j ≤ k} w j` is the number of terms `≤ k` (with
  multiplicity) of the ordered list in which each `k` appears `w k` times, and
  `nthTerm w n = sInf {k | n ≤ numLE w k}` is its `n`-th term (offset `1`). The theorems
  `a_spec` / `a354570_spec` show that, for every `n`, this infimum is attained: `a n` is the
  least `k` with at least `n` terms `≤ k` (this uses `exists_le_numLE_wE` / `..._wO`, i.e. both
  lists are infinite). So `a n` = A354571(n) and `a354570 n` = A354570(n) for `n ≥ 1`
  (`a 0 = a354570 0 = 0` are junk values that do not affect the limits).
* `a_data` checks all 58 listed terms of A354571 and `a354570_data` all 60 listed terms of
  A354570 (kernel-checked, via `nthTerm_eq_getElem_expand`, which identifies `nthTerm w (i + 1)`
  with the `i`-th entry of the explicitly expanded list).
* *The conjecture* is the conjunction of `a(n)/n → π` and `A354570(n)/n → π` as `n → ∞`, with the
  quotients taken in `ℝ`.
-/

namespace Math0.Statements.A354571

/-! ### Primitive Pythagorean triangles with a given leg -/

/-- `(x, y, z)` is a primitive Pythagorean triangle: positive legs `x, y`, hypotenuse `z`,
`x² + y² = z²`, and `gcd(x, y, z) = 1`. -/
def IsPPT (x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ Nat.gcd (Nat.gcd x y) z = 1

instance (x y z : ℕ) : Decidable (IsPPT x y z) :=
  inferInstanceAs (Decidable (0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧
    Nat.gcd (Nat.gcd x y) z = 1))

/-- The candidate `(b, c)` with `c - b = d` for a triangle with leg `k`. -/
def cand (k d : ℕ) : ℕ × ℕ := ((k ^ 2 / d - d) / 2, (k ^ 2 / d - d) / 2 + d)

/-- The primitive Pythagorean triangles having `k` as a leg, as pairs `(other leg, hypotenuse)`
(see `mem_legTriangles`). -/
def legTriangles (k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range k).filter (fun d => IsPPT (cand k d).1 k (cand k d).2)).image (cand k)

/-- `legTriangles k` is exactly the set of `(b, c)` with `(b, k, c)` a primitive Pythagorean
triangle. -/
theorem mem_legTriangles {k b c : ℕ} : (b, c) ∈ legTriangles k ↔ IsPPT b k c := by
  constructor
  · intro h
    obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp h
    have hd' := (Finset.mem_filter.mp hd).2
    rw [hdc] at hd'
    exact hd'
  · intro h
    obtain ⟨hb, hk, hsq, hg⟩ := h
    have hbc : b < c := by
      by_contra hcon
      have : c ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have : 0 < k ^ 2 := by positivity
      omega
    obtain ⟨d, rfl⟩ : ∃ d, c = b + d := ⟨c - b, by omega⟩
    have hk2 : k ^ 2 = d * (2 * b + d) := by nlinarith
    have hd0 : 0 < d := by omega
    have hdiv : k ^ 2 / d = 2 * b + d := by
      rw [hk2, Nat.mul_div_cancel_left _ hd0]
    have hcand : cand k d = (b, b + d) := by
      simp only [cand, hdiv, Prod.mk.injEq]
      omega
    have hdk : d < k := by
      have : d ^ 2 < k ^ 2 := by rw [hk2]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
    refine Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdk, ?_⟩, hcand⟩
    rw [hcand]
    exact ⟨hb, hk, hsq, hg⟩

/-! ### The two sequences -/

/-- All odd prime factors of `k` are `≡ 3 (mod 4)`, and at least one prime factor is odd. -/
def CondE (k : ℕ) : Prop :=
  (∀ p ∈ k.primeFactors, Odd p → p % 4 = 3) ∧ ∃ p ∈ k.primeFactors, Odd p

instance : DecidablePred CondE := fun k =>
  inferInstanceAs (Decidable ((∀ p ∈ k.primeFactors, Odd p → p % 4 = 3) ∧
    ∃ p ∈ k.primeFactors, Odd p))

/-- All prime factors of `k` are `≡ 3 (mod 4)`. -/
def CondO (k : ℕ) : Prop := ∀ p ∈ k.primeFactors, p % 4 = 3

instance : DecidablePred CondO := fun k =>
  inferInstanceAs (Decidable (∀ p ∈ k.primeFactors, p % 4 = 3))

/-- Multiplicity of `k` in A354571: the number of primitive Pythagorean triangles whose even leg
is `k`, if `k` satisfies `CondE`; `0` otherwise. -/
def wE (k : ℕ) : ℕ := if Even k ∧ CondE k then (legTriangles k).card else 0

/-- Multiplicity of `k` in A354570: the number of primitive Pythagorean triangles whose odd leg
is `k`, if `k` satisfies `CondO`; `0` otherwise. -/
def wO (k : ℕ) : ℕ := if Odd k ∧ CondO k then (legTriangles k).card else 0

/-- The number of terms `≤ k` of the ordered list in which each `j` occurs `w j` times. -/
def numLE (w : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), w j

/-- The `n`-th term (offset `1`) of the ordered list in which each `j` occurs `w j` times: the
least `k` such that at least `n` terms are `≤ k`. -/
noncomputable def nthTerm (w : ℕ → ℕ) (n : ℕ) : ℕ := sInf {k | n ≤ numLE w k}

/-- A354571: ordered even leg lengths `k` (listed with multiplicity) of primitive Pythagorean
triangles such that all odd prime factors of `k` are `≡ 3 (mod 4)` and at least one prime factor
is odd (offset `1`). -/
noncomputable def a (n : ℕ) : ℕ := nthTerm wE n

/-- A354570: ordered odd leg lengths `k` (listed with multiplicity) of primitive Pythagorean
triangles such that all prime factors of `k` are `≡ 3 (mod 4)` (offset `1`). -/
noncomputable def a354570 (n : ℕ) : ℕ := nthTerm wO n

/-! ### `nthTerm` is the `n`-th term -/

theorem numLE_mono (w : ℕ → ℕ) {j k : ℕ} (h : j ≤ k) : numLE w j ≤ numLE w k :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))

theorem numLE_add_le (w : ℕ → ℕ) {j k : ℕ} (h : j < k) : numLE w j + w k ≤ numLE w k := by
  unfold numLE
  have hk : k ∉ Finset.range (j + 1) := by simp; omega
  calc ∑ x ∈ Finset.range (j + 1), w x + w k
      = ∑ x ∈ insert k (Finset.range (j + 1)), w x := by rw [Finset.sum_insert hk, add_comm]
    _ ≤ ∑ x ∈ Finset.range (k + 1), w x := Finset.sum_le_sum_of_subset (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_range] at hx ⊢
        omega)

/-- If the weight `w` is positive at arbitrarily large arguments, every `n` is reached. -/
theorem exists_le_numLE (w : ℕ → ℕ) (hw : ∀ K, ∃ k, K < k ∧ 1 ≤ w k) (n : ℕ) :
    ∃ k, n ≤ numLE w k := by
  induction n with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨k', hkk', hw'⟩ := hw k
    exact ⟨k', by have := numLE_add_le w hkk'; omega⟩

/-- When the infimum is attained, `nthTerm w n` is the least `k` with `n ≤ numLE w k`. -/
theorem nthTerm_spec (w : ℕ → ℕ) {n : ℕ} (h : ∃ k, n ≤ numLE w k) :
    n ≤ numLE w (nthTerm w n) ∧ ∀ j < nthTerm w n, numLE w j < n :=
  ⟨Nat.sInf_mem h, fun _ hj => not_le.mp
    (Nat.notMem_of_lt_sInf (s := {k | n ≤ numLE w k}) hj)⟩

theorem nthTerm_eq {w : ℕ → ℕ} {n K : ℕ} (h1 : n ≤ numLE w K) (h2 : ∀ j < K, numLE w j < n) :
    nthTerm w n = K :=
  le_antisymm (Nat.sInf_le h1)
    (le_csInf ⟨K, h1⟩ fun j hj => not_lt.mp fun hlt => (Nat.lt_irrefl _) ((h2 j hlt).trans_le hj))

/-- The ordered list of all terms `< K`, each `k` repeated `w k` times. -/
def expand (w : ℕ → ℕ) (K : ℕ) : List ℕ := (List.range K).flatMap (fun k => List.replicate (w k) k)

theorem expand_succ (w : ℕ → ℕ) (K : ℕ) :
    expand w (K + 1) = expand w K ++ List.replicate (w K) K := by
  simp [expand, List.range_succ, List.flatMap_append]

theorem length_expand (w : ℕ → ℕ) (K : ℕ) :
    (expand w K).length = ∑ j ∈ Finset.range K, w j := by
  induction K with
  | zero => simp [expand]
  | succ K ih => rw [expand_succ, List.length_append, ih, List.length_replicate,
      Finset.sum_range_succ]

/-- The `i`-th entry (from `0`) of the expanded list is the `(i + 1)`-th term. -/
theorem nthTerm_eq_getElem_expand (w : ℕ → ℕ) (K : ℕ) (i : ℕ) (hi : i < (expand w K).length) :
    nthTerm w (i + 1) = (expand w K)[i] := by
  induction K generalizing i with
  | zero => simp [expand] at hi
  | succ K ih =>
    simp only [expand_succ] at hi ⊢
    by_cases hlt : i < (expand w K).length
    · rw [List.getElem_append_left hlt]
      exact ih i hlt
    · rw [List.getElem_append_right (by omega), List.getElem_replicate]
      rw [List.length_append, List.length_replicate] at hi
      have hlen := length_expand w K
      apply nthTerm_eq
      · show i + 1 ≤ ∑ j ∈ Finset.range (K + 1), w j
        rw [Finset.sum_range_succ]
        omega
      · intro j hj
        have : numLE w j ≤ ∑ j ∈ Finset.range K, w j :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
        omega

/-- Reading off the first `L` terms from the expanded list. -/
theorem map_nthTerm_eq (w : ℕ → ℕ) (K L : ℕ) (l : List ℕ)
    (h : (expand w K).take L = l ∧ L ≤ (expand w K).length) :
    (List.range L).map (fun i => nthTerm w (i + 1)) = l := by
  obtain ⟨h1, h2⟩ := h
  subst h1
  apply List.ext_getElem
  · simp [h2]
  · intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    simp only [List.length_map, List.length_range] at hi
    exact nthTerm_eq_getElem_expand w K i (by omega)

/-! ### Both lists are infinite, so `a n` and `a354570 n` are genuinely the `n`-th terms -/

theorem wE_pos (m : ℕ) : 1 ≤ wE (4 * 3 ^ (m + 1)) := by
  set u := 2 * 3 ^ (m + 1) with hu
  have hu6 : 6 ≤ u := by
    have : 3 ≤ 3 ^ (m + 1) := Nat.le_self_pow (by omega) 3
    omega
  have hk : 4 * 3 ^ (m + 1) = 2 * u := by omega
  have hcond : Even (4 * 3 ^ (m + 1)) ∧ CondE (4 * 3 ^ (m + 1)) := by
    refine ⟨⟨2 * 3 ^ (m + 1), by ring⟩, ?_⟩
    have hpf : (4 * 3 ^ (m + 1)).primeFactors = {2, 3} := by
      rw [Nat.primeFactors_mul (by norm_num) (by positivity),
        Nat.primeFactors_prime_pow (by omega) Nat.prime_three,
        show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by omega) Nat.prime_two]
      rfl
    rw [CondE, hpf]
    decide
  -- the triangle `(u² - 1, 2u, u² + 1)`
  obtain ⟨v, hv⟩ : ∃ v, u ^ 2 = v + 1 := ⟨u ^ 2 - 1, by have : 1 ≤ u ^ 2 := (by nlinarith); omega⟩
  have hv4 : 2 ∣ u := ⟨3 ^ (m + 1), hu⟩
  have hvodd : v % 2 = 1 := by
    obtain ⟨t, ht⟩ := hv4
    have : u ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
    omega
  have hppt : IsPPT v (4 * 3 ^ (m + 1)) (v + 2) := by
    refine ⟨by nlinarith, by positivity, ?_, ?_⟩
    · rw [hk]; nlinarith
    · have h1 : Nat.gcd (Nat.gcd v (4 * 3 ^ (m + 1))) (v + 2) ∣ 2 := by
        have ha : Nat.gcd (Nat.gcd v (4 * 3 ^ (m + 1))) (v + 2) ∣ v :=
          (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
        have hb : Nat.gcd (Nat.gcd v (4 * 3 ^ (m + 1))) (v + 2) ∣ v + 2 := Nat.gcd_dvd_right _ _
        exact (Nat.dvd_add_right ha).mp hb
      have h2 : Nat.gcd (Nat.gcd v (4 * 3 ^ (m + 1))) (v + 2) ∣ v :=
        (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · rw [h] at h2; omega
  have hmem : (v, v + 2) ∈ legTriangles (4 * 3 ^ (m + 1)) := mem_legTriangles.mpr hppt
  rw [wE, if_pos hcond]
  exact Finset.card_pos.mpr ⟨_, hmem⟩

theorem wO_pos (m : ℕ) : 1 ≤ wO (3 ^ (m + 1)) := by
  have hodd : Odd (3 ^ (m + 1)) := Odd.pow (by decide)
  have hcond : Odd (3 ^ (m + 1)) ∧ CondO (3 ^ (m + 1)) := by
    refine ⟨hodd, ?_⟩
    rw [CondO, Nat.primeFactors_prime_pow (by omega) Nat.prime_three]
    decide
  -- the triangle `(3^(m+1), v, v + 1)` with `3^(2(m+1)) = 2v + 1`
  obtain ⟨v, hv⟩ : ∃ v, (3 ^ (m + 1)) ^ 2 = 2 * v + 1 := (hodd.pow (n := 2))
  have h9 : 9 ≤ (3 ^ (m + 1)) ^ 2 := by
    have : 3 ≤ 3 ^ (m + 1) := Nat.le_self_pow (by omega) 3
    nlinarith
  have hppt : IsPPT v (3 ^ (m + 1)) (v + 1) := by
    refine ⟨by omega, by positivity, by nlinarith, ?_⟩
    have ha : Nat.gcd (Nat.gcd v (3 ^ (m + 1))) (v + 1) ∣ v :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hb : Nat.gcd (Nat.gcd v (3 ^ (m + 1))) (v + 1) ∣ v + 1 := Nat.gcd_dvd_right _ _
    exact Nat.dvd_one.mp ((Nat.dvd_add_right ha).mp hb)
  have hmem : (v, v + 1) ∈ legTriangles (3 ^ (m + 1)) := mem_legTriangles.mpr hppt
  rw [wO, if_pos hcond]
  exact Finset.card_pos.mpr ⟨_, hmem⟩

theorem exists_le_numLE_wE (n : ℕ) : ∃ k, n ≤ numLE wE k :=
  exists_le_numLE wE (fun K => ⟨4 * 3 ^ (K + 1), by
    have := Nat.lt_pow_self (n := K + 1) (show 1 < 3 by norm_num); omega, wE_pos K⟩) n

theorem exists_le_numLE_wO (n : ℕ) : ∃ k, n ≤ numLE wO k :=
  exists_le_numLE wO (fun K => ⟨3 ^ (K + 1), by
    have := Nat.lt_pow_self (n := K + 1) (show 1 < 3 by norm_num); omega, wO_pos K⟩) n

/-- `a n` is the least `k` such that at least `n` terms of A354571 (with multiplicity) are
`≤ k`, i.e. it is the `n`-th term of A354571. -/
theorem a_spec (n : ℕ) : n ≤ numLE wE (a n) ∧ ∀ j < a n, numLE wE j < n :=
  nthTerm_spec wE (exists_le_numLE_wE n)

/-- `a354570 n` is the least `k` such that at least `n` terms of A354570 (with multiplicity) are
`≤ k`, i.e. it is the `n`-th term of A354570. -/
theorem a354570_spec (n : ℕ) :
    n ≤ numLE wO (a354570 n) ∧ ∀ j < a354570 n, numLE wO j < n :=
  nthTerm_spec wO (exists_le_numLE_wO n)

/-! ### Data -/

/-- The definition reproduces all 58 terms of A354571 listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 58).map (fun i => a (i + 1)) =
    [12, 12, 24, 24, 28, 28, 36, 36, 44, 44, 48, 48, 56, 56, 72, 72, 76, 76, 84, 84, 84, 84, 88,
      88, 92, 92, 96, 96, 108, 108, 112, 112, 124, 124, 132, 132, 132, 132, 144, 144, 152, 152,
      168, 168, 168, 168, 172, 172, 176, 176, 184, 184, 188, 188, 192, 192, 196, 196] :=
  map_nthTerm_eq wE 197 58 _ (by decide +kernel)

/-- The definition reproduces all 60 terms of A354570 listed in OEIS (kernel-checked). -/
theorem a354570_data : (List.range 60).map (fun i => a354570 (i + 1)) =
    [3, 7, 9, 11, 19, 21, 21, 23, 27, 31, 33, 33, 43, 47, 49, 57, 57, 59, 63, 63, 67, 69, 69, 71,
      77, 77, 79, 81, 83, 93, 93, 99, 99, 103, 107, 121, 127, 129, 129, 131, 133, 133, 139, 141,
      141, 147, 147, 151, 161, 161, 163, 167, 171, 171, 177, 177, 179, 189, 189, 191] :=
  map_nthTerm_eq wO 192 60 _ (by decide +kernel)

/-! ### The conjecture -/

/-- Conjecture (Selle, A354571 and A354570): `a(n)/n → π` and `A354570(n)/n → π` as `n → ∞`. -/
def statement : Prop :=
  Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n) Filter.atTop (nhds Real.pi) ∧
    Filter.Tendsto (fun n : ℕ => (a354570 n : ℝ) / n) Filter.atTop (nhds Real.pi)

end Math0.Statements.A354571
