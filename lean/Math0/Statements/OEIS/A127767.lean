/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A127767: inverse of the triangle `1/C(n)` on `k ≤ n ≤ 2k` has integer entries

Source: https://oeis.org/A127767, Paul Barry, Jan 28 2007. Verbatim:
> It is conjectured that all elements of the triangle are integers.

The entry (offset `0`, keywords `sign,tabl`) is named "Inverse of number triangle
`A(n,k) = 1/C(n)` if `k <= n <= 2k`, 0 otherwise, where `C(n) = A000108(n)`."

## Encoding

* *Catalan numbers.* `cat n` is `C(n) = A000108(n)`, computed by the product recursion
  `C(n+1) = C(n) · 2(2n+1) / (n+2)` so that the kernel can evaluate it; `cat_eq_catalan` proves
  `cat n = catalan n` (Mathlib's Catalan numbers) for every `n`.
* *The triangle `A`.* `A n k : ℚ` is `1 / C(n)` if `k ≤ n ∧ n ≤ 2k` and `0` otherwise, exactly as
  in the name. It is an infinite lower-triangular matrix with diagonal entries
  `A(n,n) = 1/C(n) ≠ 0`, so it has a unique (lower-triangular) inverse.
* *The inverse triangle `T`.* `T n k : ℚ` is computed by forward substitution from
  `∑_{j ≤ n} A(n,j) T(j,k) = [n = k]`, i.e.
  `T(n,k) = C(n) · ([n = k] - ∑_{j < n} A(n,j) T(j,k))` for `k ≤ n` and `T(n,k) = 0` for
  `k > n` (`T_spec`, `T_eq_zero_of_lt`). The rows are built one at a time (`rows`) so the kernel
  evaluates each entry only once. That `T` really is the inverse of `A` is proved, not assumed:
  `inv_Amat` shows that for every `N` the `N × N` truncation `Tmat N` of `T` is the matrix inverse
  `(Amat N)⁻¹` (Mathlib's `Matrix.inv`) of the `N × N` truncation of `A`. (For lower-triangular
  infinite matrices the inverse is determined by these finite truncations.)
* *The sequence.* The OEIS sequence is the triangle read by rows, `0 ≤ k ≤ n`, offset `0`:
  `a m = T n k` where `m = n(n+1)/2 + k` (`rowOf m` is this `n`). Its values are a priori
  rationals, so `a : ℕ → ℚ`. `a_data` checks all `66` listed terms (rows `n = 0, …, 10`) in the
  kernel; `rows_data` checks the same rows as lists.
* *The conjecture.* `statement`: every element `T(n,k)`, `0 ≤ k ≤ n`, of the inverse triangle is
  an integer. `statement_iff_matrix` shows this is equivalent to: for every `N`, all entries of
  `(Amat N)⁻¹` are integers. (Entries with `k > n` are `0` anyway.)
-/

namespace Math0.Statements.A127767

open Finset

/-! ### Catalan numbers -/

/-- Catalan numbers `C(n) = A000108(n)` by the product recursion
`C(n+1) = C(n) · 2(2n+1) / (n+2)` (kernel-friendly; see `cat_eq_catalan`). -/
def cat : ℕ → ℕ
  | 0 => 1
  | n + 1 => cat n * (2 * (2 * n + 1)) / (n + 2)

/-- `cat` agrees with Mathlib's `catalan`. -/
theorem cat_eq_catalan (n : ℕ) : cat n = catalan n := by
  induction n with
  | zero => simp [cat]
  | succ n ih =>
    rw [cat, ih]
    have h1 := succ_mul_catalan_eq_centralBinom (n + 1)
    have h2 := succ_mul_catalan_eq_centralBinom n
    have h3 := Nat.succ_mul_centralBinom_succ n
    have key : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
      have : (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
        calc (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * Nat.centralBinom (n + 1) := by
              rw [← h1]
          _ = 2 * (2 * n + 1) * Nat.centralBinom n := h3
          _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by rw [← h2]; ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) this
    rw [show catalan n * (2 * (2 * n + 1)) = (n + 2) * catalan (n + 1) by rw [key]; ring]
    exact Nat.mul_div_cancel_left _ (by omega)

theorem cat_pos (n : ℕ) : 0 < cat n := by
  rw [cat_eq_catalan]
  have h := succ_mul_catalan_eq_centralBinom n
  have hc := Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0

/-! ### The triangle and its inverse -/

/-- The number triangle `A(n,k) = 1/C(n)` if `k ≤ n ≤ 2k`, `0` otherwise. -/
def A (n k : ℕ) : ℚ := if k ≤ n ∧ n ≤ 2 * k then 1 / (cat n : ℚ) else 0

/-- Forward substitution: from the rows `0, …, n-1` of the inverse (`n = rs.length`), row `n`
(entries `k = 0, …, n`) is `T(n,k) = C(n) · ([n = k] - ∑_{j < n} A(n,j) T(j,k))`, which solves
`∑_{j ≤ n} A(n,j) T(j,k) = [n = k]` since `A(n,n) = 1/C(n)`. -/
def nextRow (rs : List (List ℚ)) : List ℚ :=
  (List.range (rs.length + 1)).map fun k =>
    (cat rs.length : ℚ) * ((if rs.length = k then 1 else 0) -
      ∑ j ∈ range rs.length, A rs.length j * (rs.getD j []).getD k 0)

/-- The rows `0, …, n-1` of the inverse triangle. -/
def rows : ℕ → List (List ℚ)
  | 0 => []
  | n + 1 => rows n ++ [nextRow (rows n)]

/-- The inverse triangle `T(n,k)` (entry `(n,k)` of `A⁻¹`; see `inv_Amat`). -/
def T (n k : ℕ) : ℚ := ((rows (n + 1)).getD n []).getD k 0

/-- The row index `n` of position `m` when the triangle is read by rows:
the largest `n ≤ m` with `n(n+1)/2 ≤ m`. -/
def rowOf (m : ℕ) : ℕ :=
  (List.range (m + 1)).foldl (fun acc n => if n * (n + 1) / 2 ≤ m then n else acc) 0

/-- A127767: the inverse triangle `T` read by rows (`0 ≤ k ≤ n`), offset `0`. -/
def a (m : ℕ) : ℚ := T (rowOf m) (m - rowOf m * (rowOf m + 1) / 2)

/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all 66 terms. -/
theorem a_data : (List.range 66).map (fun i => a i) =
    ([1, 0, 1, 0, -1, 2, 0, 1, -2, 5, 0, 0, 0, -5, 14, 0, -1, 2, 0, -14, 42, 0, 0, 0, 0, 0, -42,
      132, 0, 1, -2, 5, 0, 0, -132, 429, 0, 0, 0, 0, 0, 0, 0, -429, 1430, 0, 0, 0, -5, 14, 0, 0,
      0, -1430, 4862, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4862, 16796] : List ℤ).map (fun z => (z : ℚ)) := by
  decide +kernel

/-- The same 66 terms, as the rows `0, …, 10` of the triangle (kernel-checked). -/
theorem rows_data : rows 11 = [[1], [0, 1], [0, -1, 2], [0, 1, -2, 5], [0, 0, 0, -5, 14],
    [0, -1, 2, 0, -14, 42], [0, 0, 0, 0, 0, -42, 132], [0, 1, -2, 5, 0, 0, -132, 429],
    [0, 0, 0, 0, 0, 0, 0, -429, 1430], [0, 0, 0, -5, 14, 0, 0, 0, -1430, 4862],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, -4862, 16796]] := by
  decide +kernel

/-! ### `T` is the inverse of `A` -/

theorem rows_length (n : ℕ) : (rows n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rows, ih]

theorem rows_getD (n j : ℕ) : (rows n).getD j [] = if j < n then nextRow (rows j) else [] := by
  induction n with
  | zero => simp [rows]
  | succ n ih =>
    rw [rows]
    rcases lt_trichotomy j n with h | h | h
    · rw [List.getD_append _ _ _ _ (by rw [rows_length]; exact h), ih, if_pos h,
        if_pos (by omega)]
    · subst h
      rw [List.getD_append_right _ _ _ _ (by rw [rows_length]), rows_length, Nat.sub_self,
        if_pos (by omega)]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by rw [rows_length]; omega), rows_length,
        if_neg (by omega)]
      obtain ⟨d, hd⟩ : ∃ d, j - n = d + 1 := ⟨j - n - 1, by omega⟩
      rw [hd]
      rfl

theorem T_eq (n k : ℕ) : T n k = (nextRow (rows n)).getD k 0 := by
  rw [T, rows_getD, if_pos (Nat.lt_succ_self n)]

/-- The forward-substitution recursion defining `T`. -/
theorem T_spec (n k : ℕ) :
    T n k = if k ≤ n then
      (cat n : ℚ) * ((if n = k then 1 else 0) - ∑ j ∈ range n, A n j * T j k) else 0 := by
  rw [T_eq, nextRow, rows_length, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hk : k ≤ n
  · rw [List.getElem?_range (by omega), if_pos hk, Option.map_some, Option.getD_some]
    congr 2
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [rows_getD, if_pos (Finset.mem_range.mp hj), ← T_eq]
  · rw [List.getElem?_eq_none (by simp; omega), if_neg hk]
    rfl

theorem T_eq_zero_of_lt {n k : ℕ} (h : n < k) : T n k = 0 := by
  rw [T_spec, if_neg (by omega)]

theorem A_self (n : ℕ) : A n n = 1 / (cat n : ℚ) := by
  rw [A, if_pos ⟨le_rfl, by omega⟩]

theorem A_eq_zero_of_lt {n x : ℕ} (h : n < x) : A n x = 0 := by
  rw [A, if_neg (by omega)]

/-- Row `n` of `A` times column `k` of `T` is `[n = k]`. -/
theorem sum_A_mul_T (n k N : ℕ) (hN : n < N) :
    ∑ x ∈ range N, A n x * T x k = if n = k then 1 else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = n + 1 + m := ⟨N - (n + 1), by omega⟩
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := range m)
    (fun x _ => by rw [A_eq_zero_of_lt (by omega), zero_mul]), add_zero, Finset.sum_range_succ,
    A_self]
  have hc : (cat n : ℚ) ≠ 0 := by exact_mod_cast (cat_pos n).ne'
  by_cases hk : k ≤ n
  · rw [T_spec n k, if_pos hk]
    field_simp
    ring
  · rw [T_eq_zero_of_lt (by omega), if_neg (by omega), mul_zero, add_zero]
    exact Finset.sum_eq_zero fun x hx => by
      rw [T_eq_zero_of_lt (by have := Finset.mem_range.mp hx; omega), mul_zero]

/-- The `N × N` truncation of the triangle `A`. -/
def Amat (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i j => A i j

/-- The `N × N` truncation of the triangle `T`. -/
def Tmat (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i j => T i j

theorem Amat_mul_Tmat (N : ℕ) : Amat N * Tmat N = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Amat, Tmat, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun x => A i x * T x j) N, sum_A_mul_T _ _ _ i.isLt]
  simp [Fin.ext_iff]

/-- `T` is the inverse of `A`: for every `N`, `(Amat N)⁻¹ = Tmat N`. -/
theorem inv_Amat (N : ℕ) : (Amat N)⁻¹ = Tmat N :=
  Matrix.inv_eq_right_inv (Amat_mul_Tmat N)

/-! ### The conjecture -/

/-- All elements `T(n,k)`, `0 ≤ k ≤ n`, of the inverse triangle are integers. -/
def statement : Prop := ∀ n k : ℕ, k ≤ n → ∃ z : ℤ, T n k = z

/-- Equivalent form: for every `N`, the inverse of the `N × N` truncation of `A` has integer
entries. -/
theorem statement_iff_matrix :
    statement ↔ ∀ (N : ℕ) (i j : Fin N), ∃ z : ℤ, (Amat N)⁻¹ i j = z := by
  constructor
  · intro h N i j
    rw [inv_Amat]
    simp only [Tmat, Matrix.of_apply]
    by_cases hji : (j : ℕ) ≤ i
    · exact h i j hji
    · exact ⟨0, by rw [T_eq_zero_of_lt (by omega)]; simp⟩
  · intro h n k hk
    obtain ⟨z, hz⟩ := h (n + 1) ⟨n, by omega⟩ ⟨k, by omega⟩
    rw [inv_Amat] at hz
    exact ⟨z, hz⟩

end Math0.Statements.A127767
