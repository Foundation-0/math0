/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A144637: parity of `(1/18) 6^n a(n) / n!` (column 2 of the inverse of A144385)

Source: https://oeis.org/A144637, Peter Bala, Feb 19 2026 (FORMULA section). Verbatim:
> Conjecture: (1/18)*6^(n)*a(n)/n! is odd iff n = 2^k for k >= 1.

The entry (offset `0`, keywords `sign,easy`) is named "Column 2 of triangle in A144633."
A144633 (offset `0`) is the "Triangle of 3-restricted Stirling numbers of the first kind
(T(n,k), 0 <= k <= n), read by rows", with the definition "take the triangle in A144385, write
it as an (infinite) upper triangular square matrix, invert it and transpose it." A144385 is the
"Triangle read by rows: T(n,k) is the number of partitions of [1, 2, ..., k] into exactly n
blocks, each of size 1, 2 or 3 (n >= 0, 0 <= k <= 3n)", with the formula
"T(n, k) = T(n - 1, k - 1) + (k - 1)*T(n - 1, k - 2) + (1/2)*(k - 1)*(k - 2)*T(n - 1, k - 3)".
Just before the conjecture the entry says that `(1/18)*A(6*x) = x^2 - 6*x^3 + 33*x^4 - ...`
(`A` the e.g.f. of the sequence) "appears to be an integral series".

## Encoding

* *A144385.* `S n k : ℕ` is A144385 `T(n,k)`. Row `0` is `[1]` and row `n+1` is built from row
  `n` by the A144385 recurrence (this is also how the OEIS Maple/Mathematica programs compute it;
  the recurrence is the usual case split on whether the element `k` lies in a block of size `1`,
  `2` or `3`). The rows are stored as lists (`srow`) so the kernel computes each entry once.
  `S_zero` and `S_succ` prove that `S` satisfies exactly row `0` and the A144385 recurrence for
  every `n` and `k` (terms with a negative index are `0`), which determine it uniquely;
  `S_data` checks all `70` listed terms of A144385 (rows `0, …, 6`).
* *A144633.* Write `M` for the infinite upper triangular matrix `M(i,j) = S i j` (`S_eq_zero_of_lt`,
  `S_self`: it is unitriangular). Its inverse `R = M⁻¹` is upper triangular, and A144633 is
  `T(n,k) = R(k,n)`. From `R M = 1`, forward substitution gives, for `k ≤ n`,
  `T(n,k) = [n = k] - ∑_{j < n} T(j,k) S(j,n)` and `T(n,k) = 0` for `k > n` (`T_spec`); `T n k : ℤ`
  is computed by this recursion, row by row (`trows`). That this really is the transposed inverse
  is proved, not assumed: `Tmat_eq` shows that for every `N` the `N × N` truncation of `T` is the
  transpose of Mathlib's matrix inverse `(Mmat N)⁻¹` of the `N × N` truncation of `M` (for
  upper triangular infinite matrices the inverse is determined by these truncations).
  `T_data` checks all `55` listed terms of A144633 (rows `0, …, 9`).
* *The sequence.* `a n = T n 2 : ℤ` (column `2`, offset `0`; the values are signed).
  `a_data` checks all `23` listed terms `a(0), …, a(22)`.
* *The quantity.* `y n = (1/18) · 6^n · a(n) / n!` is computed in `ℚ`, literally as written.
  `y_data` checks that `y 0, …, y 8` are the coefficients `0, 0, 1, -6, 33, -162, 630, -972,
  -14499` of the series `(1/18) A(6x)` displayed in the entry.
* *The conjecture.* "`y(n)` is odd" is read as "`y(n)` is an odd integer":
  `∃ m : ℤ, Odd m ∧ y n = m`. The range is all `n ≥ 0` (the offset of the entry), and
  "`n = 2^k` for `k >= 1`" is `∃ k, 1 ≤ k ∧ n = 2^k`. The separate observation that every `y(n)`
  appears to be an integer is not part of the conjecture and is not included in `statement`.
-/

namespace Math0.Statements.A144637

open Finset

/-! ### A144385: partitions of `[k]` into `n` blocks of size `1`, `2` or `3` -/

/-- One step of the A144385 recurrence: from row `n` (the list `r` of entries `k = 0, …, 3n`)
build row `n + 1` (entries `k = 0, …, 3n + 3`) by
`T(n+1,k) = T(n,k-1) + (k-1) T(n,k-2) + (1/2)(k-1)(k-2) T(n,k-3)`, terms with a negative index
being `0`. -/
def nextSRow (r : List ℕ) : List ℕ :=
  (List.range (r.length + 3)).map fun k =>
    (if 1 ≤ k then r.getD (k - 1) 0 else 0) +
    (if 2 ≤ k then (k - 1) * r.getD (k - 2) 0 else 0) +
    (if 3 ≤ k then (k - 1) * (k - 2) / 2 * r.getD (k - 3) 0 else 0)

/-- Row `n` of A144385 (entries `k = 0, …, 3n`). -/
def srow : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => nextSRow (srow n)

/-- A144385 `T(n,k)`: the number of partitions of `{1, …, k}` into exactly `n` blocks, each of
size `1`, `2` or `3` (computed by the recurrence; see `S_zero`, `S_succ`). It is `0` for
`k > 3n`. -/
def S (n k : ℕ) : ℕ := (srow n).getD k 0

/-- All 70 listed terms of A144385 (rows `0, …, 6`, kernel-checked). -/
theorem S_data : (List.range 7).map (fun n => (List.range (3 * n + 1)).map (S n)) =
    [[1], [0, 1, 1, 1], [0, 0, 1, 3, 7, 10, 10], [0, 0, 0, 1, 6, 25, 75, 175, 280, 280],
      [0, 0, 0, 0, 1, 10, 65, 315, 1225, 3780, 9100, 15400, 15400],
      [0, 0, 0, 0, 0, 1, 15, 140, 980, 5565, 26145, 102025, 323400, 800800, 1401400, 1401400],
      [0, 0, 0, 0, 0, 0, 1, 21, 266, 2520, 19425, 125895, 695695, 3273270, 12962950, 42042000,
        106506400, 190590400, 190590400]] := by
  decide +kernel

theorem srow_length (n : ℕ) : (srow n).length = 3 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [srow, nextSRow, ih]; ring

/-- Row `0` of A144385: `T(0,0) = 1` and `T(0,k) = 0` for `k > 0`. -/
theorem S_zero (k : ℕ) : S 0 k = if k = 0 then 1 else 0 := by
  rcases k with _ | k
  · rfl
  · simp [S, srow]

/-- The A144385 recurrence
`T(n+1,k) = T(n,k-1) + (k-1) T(n,k-2) + (1/2)(k-1)(k-2) T(n,k-3)`, for all `n` and `k`
(terms with a negative index are `0`; `(k-1)(k-2)` is even, so `/ 2` is exact). -/
theorem S_succ (n k : ℕ) : S (n + 1) k =
    (if 1 ≤ k then S n (k - 1) else 0) +
    (if 2 ≤ k then (k - 1) * S n (k - 2) else 0) +
    (if 3 ≤ k then (k - 1) * (k - 2) / 2 * S n (k - 3) else 0) := by
  have hz : ∀ j, 3 * n + 1 ≤ j → S n j = 0 := fun j hj => by
    rw [S, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [srow_length]; exact hj)]
    rfl
  rw [S, srow, nextSRow, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hk : k < (srow n).length + 3
  · rw [List.getElem?_range hk, Option.map_some, Option.getD_some]
    rfl
  · rw [srow_length] at hk
    rw [List.getElem?_eq_none (by simp [srow_length]; omega), Option.map_none, Option.getD_none,
      if_pos (by omega), if_pos (by omega), if_pos (by omega), hz _ (by omega), hz _ (by omega),
      hz _ (by omega)]
    simp

/-- `T(j,n) = 0` for `n < j`: the matrix `M(i,j) = T(i,j)` is upper triangular. -/
theorem S_eq_zero_of_lt : ∀ {j n : ℕ}, n < j → S j n = 0 := by
  intro j
  induction j with
  | zero => intro n h; omega
  | succ j ih =>
    intro n h
    rw [S_succ]
    have h1 : 1 ≤ n → S j (n - 1) = 0 := fun _ => ih (by omega)
    have h2 : 2 ≤ n → S j (n - 2) = 0 := fun _ => ih (by omega)
    have h3 : 3 ≤ n → S j (n - 3) = 0 := fun _ => ih (by omega)
    split_ifs <;> simp_all

/-- `T(n,n) = 1`: the matrix `M(i,j) = T(i,j)` has unit diagonal. -/
theorem S_self (n : ℕ) : S n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [S_succ, if_pos (by omega), show n + 1 - 1 = n by omega, ih]
    have h2 : 2 ≤ n + 1 → S n (n + 1 - 2) = 0 := fun _ => S_eq_zero_of_lt (by omega)
    have h3 : 3 ≤ n + 1 → S n (n + 1 - 3) = 0 := fun _ => S_eq_zero_of_lt (by omega)
    split_ifs <;> simp_all

/-! ### A144633: the transposed inverse of the upper triangular matrix of A144385 -/

/-- Forward substitution for `R M = 1` (`M(j,n) = S j n`, `R = M⁻¹`, `T(n,k) = R(k,n)`): from
the rows `0, …, n-1` of `T` (`n = rs.length`), row `n` (entries `k = 0, …, n`) is
`T(n,k) = [n = k] - ∑_{j < n} T(j,k) S(j,n)`, which solves `∑_{j ≤ n} R(k,j) M(j,n) = [k = n]`
since `M(n,n) = 1`. -/
def nextTRow (rs : List (List ℤ)) : List ℤ :=
  (List.range (rs.length + 1)).map fun k =>
    (if rs.length = k then 1 else 0) -
      ∑ j ∈ range rs.length, (rs.getD j []).getD k 0 * (S j rs.length : ℤ)

/-- The rows `0, …, n-1` of A144633. -/
def trows : ℕ → List (List ℤ)
  | 0 => []
  | n + 1 => trows n ++ [nextTRow (trows n)]

/-- A144633 `T(n,k)`: entry `(k,n)` of the inverse of the upper triangular matrix
`M(i,j) = S i j` of A144385 (see `Tmat_eq`); it is `0` for `k > n`. -/
def T (n k : ℕ) : ℤ := ((trows (n + 1)).getD n []).getD k 0

/-- All 55 listed terms of A144633 (rows `0, …, 9`, kernel-checked). -/
theorem T_data : (List.range 10).map (fun n => (List.range (n + 1)).map (T n)) =
    [[1], [0, 1], [0, -1, 1], [0, 2, -3, 1], [0, -5, 11, -6, 1], [0, 10, -45, 35, -10, 1],
      [0, 35, 175, -210, 85, -15, 1], [0, -910, -315, 1225, -700, 175, -21, 1],
      [0, 11935, -6265, -5670, 5565, -1890, 322, -28, 1],
      [0, -134750, 139755, -5005, -39270, 19425, -4410, 546, -36, 1]] := by
  decide +kernel

theorem trows_length (n : ℕ) : (trows n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [trows, ih]

theorem trows_getD (n j : ℕ) :
    (trows n).getD j [] = if j < n then nextTRow (trows j) else [] := by
  induction n with
  | zero => simp [trows]
  | succ n ih =>
    rw [trows]
    rcases lt_trichotomy j n with h | h | h
    · rw [List.getD_append _ _ _ _ (by rw [trows_length]; exact h), ih, if_pos h,
        if_pos (by omega)]
    · subst h
      rw [List.getD_append_right _ _ _ _ (by rw [trows_length]), trows_length, Nat.sub_self,
        if_pos (by omega)]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by rw [trows_length]; omega), trows_length,
        if_neg (by omega)]
      obtain ⟨d, hd⟩ : ∃ d, j - n = d + 1 := ⟨j - n - 1, by omega⟩
      rw [hd]
      rfl

theorem T_eq (n k : ℕ) : T n k = (nextTRow (trows n)).getD k 0 := by
  rw [T, trows_getD, if_pos (Nat.lt_succ_self n)]

/-- The forward-substitution recursion defining `T`. -/
theorem T_spec (n k : ℕ) :
    T n k = if k ≤ n then
      (if n = k then 1 else 0) - ∑ j ∈ range n, T j k * (S j n : ℤ) else 0 := by
  rw [T_eq, nextTRow, trows_length, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hk : k ≤ n
  · rw [List.getElem?_range (by omega), if_pos hk, Option.map_some, Option.getD_some]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [trows_getD, if_pos (Finset.mem_range.mp hj), ← T_eq]
  · rw [List.getElem?_eq_none (by simp; omega), if_neg hk]
    rfl

theorem T_eq_zero_of_lt {n k : ℕ} (h : n < k) : T n k = 0 := by
  rw [T_spec, if_neg (by omega)]

/-- Row `k` of `R = Tᵀ` times column `n` of `M` is `[k = n]`. -/
theorem sum_T_mul_S (k n N : ℕ) (hN : n < N) :
    ∑ j ∈ range N, T j k * (S j n : ℤ) = if k = n then 1 else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = n + 1 + m := ⟨N - (n + 1), by omega⟩
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := range m)
    (fun x _ => by rw [S_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]), add_zero,
    Finset.sum_range_succ, S_self, Nat.cast_one, mul_one]
  by_cases hk : k ≤ n
  · rw [T_spec n k, if_pos hk]
    by_cases hnk : n = k
    · rw [if_pos hnk, if_pos hnk.symm]; ring
    · rw [if_neg hnk, if_neg (Ne.symm hnk)]; ring
  · rw [T_eq_zero_of_lt (by omega), if_neg (by omega), add_zero]
    exact Finset.sum_eq_zero fun x hx => by
      rw [T_eq_zero_of_lt (by have := Finset.mem_range.mp hx; omega), zero_mul]

/-- The `N × N` truncation of the upper triangular matrix `M(i,j) = S i j` (A144385). -/
def Mmat (N : ℕ) : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun i j => (S i j : ℤ)

/-- The `N × N` truncation of the triangle `T` (A144633), `Tmat N n k = T n k`. -/
def Tmat (N : ℕ) : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun i j => T i j

open Matrix in
theorem Tmat_transpose_mul_Mmat (N : ℕ) : (Tmat N)ᵀ * Mmat N = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Tmat, Mmat, Matrix.transpose_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun x => T x i * (S x j : ℤ)) N, sum_T_mul_S _ _ _ j.isLt]
  simp [Fin.ext_iff]

open Matrix in
/-- A144633 is the transpose of the inverse of the upper triangular matrix of A144385: for every
`N`, `Tmat N = ((Mmat N)⁻¹)ᵀ` (Mathlib's `Matrix.inv`). -/
theorem Tmat_eq (N : ℕ) : Tmat N = ((Mmat N)⁻¹)ᵀ := by
  rw [Matrix.inv_eq_left_inv (Tmat_transpose_mul_Mmat N), Matrix.transpose_transpose]

/-! ### A144637 -/

/-- A144637: column `2` of the triangle A144633, `a(n) = T(n,2)` (offset `0`). -/
def a (n : ℕ) : ℤ := T n 2

/-- The definition reproduces all 23 terms listed in OEIS, `a 0, …, a 22` (kernel-checked). -/
theorem a_data : (List.range 23).map (fun i => a (i + 0)) =
    [0, 0, 1, -3, 11, -45, 175, -315, -6265, 139755, -2127125, 28153125, -327452125,
      2921393475, -2998820825, -788463550875, 28464750689375, -739460838241125,
      16173782241491875, -294957734383186875, 3672958879661946875, 19544468129733421875,
      -3601613031568517590625] := by
  decide +kernel

/-- The quantity of the conjecture, `(1/18) · 6^n · a(n) / n!`, as a rational number. -/
def y (n : ℕ) : ℚ := (1 / 18) * 6 ^ n * (a n : ℚ) / (n.factorial : ℚ)

/-- `y 0, …, y 8` are the coefficients `0, 0, 1, -6, 33, -162, 630, -972, -14499` of the series
`(1/18) A(6x) = x^2 - 6x^3 + 33x^4 - 162x^5 + 630x^6 - 972x^7 - 14499x^8 + ⋯` displayed in the
entry (kernel-checked). -/
theorem y_data : (List.range 9).map y =
    ([0, 0, 1, -6, 33, -162, 630, -972, -14499] : List ℤ).map (fun z => (z : ℚ)) := by
  decide +kernel

/-- Conjecture (Peter Bala, 2026): for every `n ≥ 0`, `(1/18) · 6^n · a(n) / n!` is odd (i.e. it
is an odd integer) if and only if `n = 2^k` for some `k ≥ 1`. -/
def statement : Prop :=
  ∀ n : ℕ, (∃ m : ℤ, Odd m ∧ y n = (m : ℚ)) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k

end Math0.Statements.A144637
