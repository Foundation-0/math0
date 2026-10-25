/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A127752: row sums of the inverse of the `1/(3n+1)` band triangle, mod 2

Source: https://oeis.org/A127752, Paul Barry, Jan 28 2007. Verbatim:
> a(n) mod 2 is first Feigenbaum symbolic sequence A035263 (conjecture).

followed in the entry by: "The conjecture is true at least up to 2048 first terms. (But please
note the different indexing, here 0-based.) - Antti Karttunen, Sep 29 2018".

The entry (offset `0`, keyword `nonn`) is named "Row sums of inverse of number triangle
`A(n,k) = 1/(3n+1)` if `k <= n <= 2k`, 0 otherwise."

## Encoding

* *The triangle.* `A n k : ℚ` is `1/(3n+1)` if `k ≤ n ∧ n ≤ 2k` and `0` otherwise, exactly as in
  the name. It is an infinite lower-triangular matrix with nonzero diagonal `A(n,n) = 1/(3n+1)`,
  so it has a unique lower-triangular inverse, whose leading `N × N` block is the inverse of the
  leading `N × N` block `Amat N` of `A` (this is also how the OEIS programs compute it, with a
  fixed `128 × 128` truncation).
* *The sequence.* The vector of row sums `s = A⁻¹ 𝟙` is the unique solution of `A s = 𝟙`; forward
  substitution gives `s(n) = (3n+1) (1 - ∑_{j<n} A(n,j) s(j)) = 3n+1 - ∑_{j<n, n ≤ 2j} s(j)`.
  `a n : ℤ` is computed by this recursion (the values are built as a list, `vals`, so that the
  kernel evaluates each one only once; `a_rec` is the recursion). That `a` really gives the row
  sums of the inverse is proved, not assumed: `a_spec` shows that for every `N` and every
  `n < N`, `a n` equals the `n`-th row sum `∑_j (Amat N)⁻¹ n j` of Mathlib's matrix inverse of
  the `N × N` truncation. In particular the row sums are integers, so "`a(n) mod 2`" makes sense;
  it is encoded as `a n % 2` (which is `0` or `1`).
* *A035263.* Its OEIS name is "Trajectory of 1 under the morphism `0 -> 11, 1 -> 10`" (offset
  `1`). `word k` is the `k`-th iterate of the morphism `sigma` applied to the word `1`; it has
  length `2^k` (`word_length`) and is a prefix of `word (k+1)` (`word_prefix`), so the words
  converge to an infinite word whose `n`-th letter (`n ≥ 1`) is `A035263 n`. We take this letter
  from `word n` (length `2^n ≥ n`); `A035263_eq` shows that any `word k` with `n ≤ 2^k` gives
  the same letter. `A035263_data` checks all `105` listed terms of A035263.
* *Indexing.* A127752 has offset `0` and A035263 has offset `1`; as Karttunen's note says, the
  sequences are matched term by term from their first terms, i.e. `a(n) mod 2 = A035263(n+1)`
  for all `n ≥ 0`.
* *The conjecture.* `statement : ∀ n, a n % 2 = A035263 (n + 1)`.
-/

namespace Math0.Statements.A127752

open Finset Matrix

/-! ### The triangle and the row sums of its inverse -/

/-- The number triangle `A(n,k) = 1/(3n+1)` if `k ≤ n ≤ 2k`, `0` otherwise. -/
def A (n k : ℕ) : ℚ := if k ≤ n ∧ n ≤ 2 * k then 1 / (3 * n + 1 : ℚ) else 0

/-- Forward substitution for `A s = 𝟙`: from `l = [s 0, …, s (n-1)]` (`n = l.length`) the next
value is `s n = 3n+1 - ∑_{j < n, n ≤ 2j} s j`. -/
def next (l : List ℤ) : ℤ :=
  3 * l.length + 1 - ∑ j ∈ range l.length, if l.length ≤ 2 * j then l.getD j 0 else 0

/-- `vals n = [a 0, …, a (n-1)]`. -/
def vals : ℕ → List ℤ
  | 0 => []
  | n + 1 => vals n ++ [next (vals n)]

/-- A127752: the `n`-th row sum of the inverse of the triangle `A` (see `a_spec`). -/
def a (n : ℕ) : ℤ := (vals (n + 1)).getD n 0

set_option maxRecDepth 100000 in
/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all 106 listed
terms `a(0), …, a(105)`. -/
theorem a_data : (List.range 106).map (fun i => a (i + 0)) =
    [1, 4, 3, 7, 3, 6, 3, 10, 3, 6, 3, 9, 3, 6, 3, 13, 3, 6, 3, 9, 3, 6, 3, 12, 3, 6, 3, 9, 3, 6,
      3, 16, 3, 6, 3, 9, 3, 6, 3, 12, 3, 6, 3, 9, 3, 6, 3, 15, 3, 6, 3, 9, 3, 6, 3, 12, 3, 6, 3, 9,
      3, 6, 3, 19, 3, 6, 3, 9, 3, 6, 3, 12, 3, 6, 3, 9, 3, 6, 3, 15, 3, 6, 3, 9, 3, 6, 3, 12, 3, 6,
      3, 9, 3, 6, 3, 18, 3, 6, 3, 9, 3, 6, 3, 12, 3, 6] := by
  decide +kernel

/-! ### `a` gives the row sums of the inverse -/

theorem vals_length (n : ℕ) : (vals n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [vals, ih]

theorem vals_getD (n j : ℕ) : (vals n).getD j 0 = if j < n then next (vals j) else 0 := by
  induction n with
  | zero => simp [vals]
  | succ n ih =>
    rw [vals]
    rcases lt_trichotomy j n with h | h | h
    · rw [List.getD_append _ _ _ _ (by rw [vals_length]; exact h), ih, if_pos h,
        if_pos (by omega)]
    · subst h
      rw [List.getD_append_right _ _ _ _ (by rw [vals_length]), vals_length, Nat.sub_self,
        if_pos (by omega)]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by rw [vals_length]; omega), vals_length,
        if_neg (by omega)]
      obtain ⟨d, hd⟩ : ∃ d, j - n = d + 1 := ⟨j - n - 1, by omega⟩
      rw [hd]
      rfl

theorem a_eq_next (n : ℕ) : a n = next (vals n) := by
  rw [a, vals_getD, if_pos (Nat.lt_succ_self n)]

/-- The forward-substitution recursion: `a n = 3n+1 - ∑_{j < n, n ≤ 2j} a j`. -/
theorem a_rec (n : ℕ) :
    a n = 3 * n + 1 - ∑ j ∈ range n, if n ≤ 2 * j then a j else 0 := by
  rw [a_eq_next, next, vals_length]
  refine congrArg (fun s => (3 * (n : ℤ) + 1) - s) (Finset.sum_congr rfl fun j hj => ?_)
  rw [vals_getD, if_pos (Finset.mem_range.mp hj), ← a_eq_next]

/-- Row `n` of `A` applied to the vector `a` gives `1`. -/
theorem sum_A_mul_a (n N : ℕ) (hN : n < N) : ∑ j ∈ range N, A n j * (a j : ℚ) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = n + 1 + m := ⟨N - (n + 1), by omega⟩
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := range m)
    (fun x _ => by rw [A, if_neg (by omega), zero_mul]), add_zero, Finset.sum_range_succ]
  have h3 : (3 * n + 1 : ℚ) ≠ 0 := by positivity
  have hsum : ∑ j ∈ range n, A n j * (a j : ℚ) =
      (1 / (3 * n + 1 : ℚ)) * ((∑ j ∈ range n, if n ≤ 2 * j then a j else 0 : ℤ) : ℚ) := by
    rw [Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    by_cases h : n ≤ 2 * j
    · rw [A, if_pos ⟨hj.le, h⟩, if_pos h]
    · rw [A, if_neg (fun h' => h h'.2), if_neg h]
      simp
  have hrec := a_rec n
  rw [hsum, A, if_pos ⟨le_rfl, by omega⟩]
  have hrecQ : (a n : ℚ) = 3 * n + 1 -
      ((∑ j ∈ range n, if n ≤ 2 * j then a j else 0 : ℤ) : ℚ) := by
    rw [hrec]; push_cast; ring
  rw [hrecQ]
  field_simp
  ring

/-- The `N × N` truncation of the triangle `A`. -/
def Amat (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i j => A i j

theorem Amat_isLowerTriangular (N : ℕ) : (Amat N).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  simp only [Amat, Matrix.of_apply, A]
  rw [if_neg (fun h => absurd h.1 (by simpa using hij'))]

theorem Amat_det_ne_zero (N : ℕ) : (Amat N).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (Amat_isLowerTriangular N)]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  simp only [Amat, Matrix.of_apply, A]
  rw [if_pos ⟨le_rfl, by omega⟩]
  positivity

theorem Amat_mulVec_a (N : ℕ) : Amat N *ᵥ (fun j : Fin N => (a j : ℚ)) = fun _ => 1 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Amat, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun x => A i x * (a x : ℚ)) N]
  exact sum_A_mul_a _ _ i.isLt

/-- `a` gives the row sums of the inverse of `A`: for every `N` and every `n < N`, `a n` is the
sum of row `n` of `(Amat N)⁻¹`, the (Mathlib) inverse of the `N × N` truncation of `A`. -/
theorem a_spec (N : ℕ) (i : Fin N) : (a i : ℚ) = ∑ j, (Amat N)⁻¹ i j := by
  have hu : IsUnit (Amat N).det := isUnit_iff_ne_zero.mpr (Amat_det_ne_zero N)
  have h := congrArg (fun v => (Amat N)⁻¹ *ᵥ v) (Amat_mulVec_a N)
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at h
  rw [congrFun h i]
  simp [Matrix.mulVec, dotProduct]

/-! ### A035263: the first Feigenbaum symbolic sequence -/

/-- The morphism `0 ↦ 11, 1 ↦ 10` (only the letters `0`, `1` ever occur). -/
def sigma (x : ℕ) : List ℕ := if x = 0 then [1, 1] else [1, 0]

/-- `word k = sigma^k (1)`, the `k`-th step of the trajectory of `1` under `sigma`. -/
def word : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => (word k).flatMap sigma

/-- A035263 (offset `1`): the `n`-th letter of the trajectory of `1` under `0 ↦ 11, 1 ↦ 10`,
read off `word n`, which has `2^n ≥ n` letters (any `word k` with `2^k ≥ n` gives the same
letter, see `A035263_eq`). -/
def A035263 (n : ℕ) : ℕ := (word n).getD (n - 1) 0

/-- The definition reproduces all 105 terms of A035263 listed in OEIS (kernel-checked). -/
theorem A035263_data : (List.range 105).map (fun i => A035263 (i + 1)) =
    [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1,
      0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
      1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1,
      0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1] := by
  decide +kernel

theorem word_length (k : ℕ) : (word k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [word, List.length_flatMap, pow_succ, ← ih]
    have : ∀ x ∈ word k, (sigma x).length = 2 := fun x _ => by
      unfold sigma; split <;> rfl
    rw [List.map_congr_left this, List.map_const', List.sum_replicate, smul_eq_mul]

theorem word_prefix (k : ℕ) : word k <+: word (k + 1) := by
  induction k with
  | zero => exact ⟨[0], rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap sigma, ?_⟩
    rw [word, word, ← ht, List.flatMap_append]

theorem word_prefix_of_le {k l : ℕ} (h : k ≤ l) : word k <+: word l := by
  induction l, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ l _ ih => exact ih.trans (word_prefix l)

/-- The letter `A035263 n` (`n ≥ 1`) is the `n`-th letter of every `word k` with `n ≤ 2^k`. -/
theorem A035263_eq {n k : ℕ} (hn : 1 ≤ n) (hk : n ≤ 2 ^ k) :
    A035263 n = (word k).getD (n - 1) 0 := by
  have hn' : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
  have key : ∀ {k l : ℕ}, k ≤ l → n ≤ 2 ^ k →
      (word k).getD (n - 1) 0 = (word l).getD (n - 1) 0 := by
    intro k l hkl hk
    have hlt : n - 1 < (word k).length := by rw [word_length]; omega
    rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _
      (lt_of_lt_of_le hlt (word_prefix_of_le hkl).length_le)]
    exact (word_prefix_of_le hkl).getElem hlt
  rw [A035263]
  rcases le_total n k with h | h
  · exact key h hn'
  · exact (key h hk).symm

/-! ### The conjecture -/

/-- `a(n) mod 2` is the first Feigenbaum symbolic sequence A035263, with A127752 indexed from
`0` and A035263 from `1`: `a(n) mod 2 = A035263(n+1)` for every `n ≥ 0`. -/
def statement : Prop := ∀ n : ℕ, a n % 2 = (A035263 (n + 1) : ℤ)

end Math0.Statements.A127752
