/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A126127: bivariate generating function of the inverse square of A061554

Source: https://oeis.org/A126127, Robert Israel, Jul 07 2019 (FORMULA section). Verbatim:
> G.f. as triangle (conjectured): (1-x)*(1-x+x^2)/(1-x*y+3*x^2-x^3*y+x^4). - _Robert Israel_, Jul 07 2019

The entry (Gary W. Adamson, Dec 17 2006; keywords `tabl,sign`, offset `0`) is named "Inverse
square of A061554." Its formula section says: "Given M = Pascal's triangle with descending row
terms, (A061554); A126127 = M^(-2)."

## Encoding

* *The triangle M.* A061554 read as a triangle is `M(n,k) = binomial(n, floor((n-k)/2))` for
  `0 ≤ k ≤ n` (Barry's and Bala's formula in A061554, equivalent to the formula
  `binomial(n, floor((n+1)/2 - (-1)^(n-k)*(k+1)/2))` there and to the Maple program of
  A126127). `M n k : ℤ` is this for `k ≤ n` and `0` above the diagonal, so `M` is an infinite
  lower-triangular matrix with `M(n,n) = 1`.
* *The inverse.* An infinite lower unitriangular matrix has a unique lower-triangular inverse,
  and its leading `L × L` block is the inverse of the leading `L × L` block of `M` (this is also
  how the Maple program of the entry computes it, with a `20 × 20` truncation). `Minv n k` is
  computed by forward substitution for `M · N = 1`, i.e.
  `N(n,k) = [k = n] - ∑_{j<n} M(n,j) N(j,k)` for `k ≤ n` and `N(n,k) = 0` for `k > n`
  (`Minv_rec`, `Minv_eq_zero`); the rows are built as lists (`invRows`) so that the kernel
  evaluates each entry once.
* *The triangle T = M^(-2).* `T n k = ∑_{j ≤ n} N(n,j) N(j,k)`, the `(n,k)` entry of `N · N`.
  That this really is `M^(-2)` is proved, not assumed: `T_spec` shows that for every `L` the
  `L × L` matrix `(T i j)_{i,j<L}` equals `Mmat L ^ (-2 : ℤ)`, the (Mathlib) `-2`-nd power of the
  `L × L` truncation `Mmat L` of `M`.
* *The sequence.* A126127 is the triangle read by rows: term `i` (offset `0`) is `T(n,k)` where
  `(n,k) = pos i` enumerates `(0,0), (1,0), (1,1), (2,0), …` (`pos_spec`:
  `pos (n(n+1)/2 + k) = (n,k)` for `k ≤ n`). `a_data` checks all 66 listed terms (rows `0..10`).
* *The conjecture.* "G.f. as triangle" is the bivariate generating function
  `G(x,y) = ∑_{n ≥ 0} ∑_{k=0}^{n} T(n,k) x^n y^k` (`x` marks the row, `y` the column). It is
  encoded as the formal power series `gf` in two variables `X 0 = x`, `X 1 = y` with rational
  coefficients (`coeff_gf`: the coefficient of `x^n y^k` is `T(n,k)` for `k ≤ n`, else `0`),
  and the conjecture says
  `gf = (1-x)(1-x+x^2) · (1-xy+3x^2-x^3y+x^4)⁻¹` in `MvPowerSeries (Fin 2) ℚ`; the denominator
  has constant coefficient `1`, so its inverse is the usual formal inverse. `statement_iff`
  records the equivalent cleared-denominator form `gf · (1-xy+3x^2-x^3y+x^4) = (1-x)(1-x+x^2)`.
  The conjecture concerns all rows `n ≥ 0` and all columns `0 ≤ k ≤ n`; no range is excluded.
-/

namespace Math0.Statements.A126127

open Finset

/-! ### The triangle A061554 and its inverse -/

/-- A061554 read as a triangle: `M(n,k) = binomial(n, floor((n-k)/2))` for `0 ≤ k ≤ n`, and `0`
above the diagonal. -/
def M (n k : ℕ) : ℤ := if k ≤ n then (n.choose ((n - k) / 2) : ℤ) else 0

/-- Forward substitution for `M · N = 1`: from `rows = [row 0 of N, …, row (n-1) of N]`
(`n = rows.length`) it computes row `n` of `N`, namely
`N(n,k) = [k = n] - ∑_{j<n} M(n,j) N(j,k)` for `k = 0, …, n`. -/
def nextRow (rows : List (List ℤ)) : List ℤ :=
  (List.range (rows.length + 1)).map fun k =>
    (if k = rows.length then 1 else 0) -
      ∑ j ∈ range rows.length, M rows.length j * (rows.getD j []).getD k 0

/-- `invRows n = [row 0 of N, …, row (n-1) of N]`. -/
def invRows : ℕ → List (List ℤ)
  | 0 => []
  | n + 1 => invRows n ++ [nextRow (invRows n)]

/-- The inverse `N = M⁻¹` of the triangle A061554 (see `Nmat_eq_inv`). -/
def Minv (n k : ℕ) : ℤ := ((invRows (n + 1)).getD n []).getD k 0

/-- A126127 as a triangle: `T = M^(-2) = N · N`, `T(n,k) = ∑_{j ≤ n} N(n,j) N(j,k)`
(see `T_spec`). -/
def T (n k : ℕ) : ℤ := ∑ j ∈ range (n + 1), Minv n j * Minv j k

/-- The position `(n,k)` (row `n`, column `k ≤ n`) of the `i`-th term of a triangle read by
rows: `(0,0), (1,0), (1,1), (2,0), (2,1), (2,2), …` (see `pos_spec`). -/
def pos : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | i + 1 =>
    match pos i with
    | (n, k) => if k < n then (n, k + 1) else (n + 1, 0)

/-- A126127: the triangle `T = M^(-2)` read by rows (offset `0`). -/
def a (i : ℕ) : ℤ := T (pos i).1 (pos i).2

/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all 66 listed
terms `a(0), …, a(65)`, i.e. rows `0` to `10` of the triangle. -/
theorem a_data : (List.range 66).map (fun i => a (i + 0)) =
    [1, -2, 1, -1, -2, 1, 5, -3, -2, 1, 2, 9, -5, -2, 1, -13, 9, 13, -7, -2, 1, -5, -33, 20, 17,
      -9, -2, 1, 34, -27, -61, 35, 21, -11, -2, 1, 13, 111, -73, -97, 54, 25, -13, -2, 1, -89,
      80, 248, -151, -141, 77, 29, -15, -2, 1, -34, -355, 252, 461, -269, -193, 104, 33, -17, -2,
      1] := by
  decide +kernel

/-! ### The enumeration of the triangle -/

theorem pos_succ (i : ℕ) : pos (i + 1) =
    if (pos i).2 < (pos i).1 then ((pos i).1, (pos i).2 + 1) else ((pos i).1 + 1, 0) := by
  rw [pos]

/-- Term number `n(n+1)/2 + k` of the triangle read by rows is in row `n`, column `k`. -/
theorem pos_spec (n k : ℕ) (hk : k ≤ n) : pos (n * (n + 1) / 2 + k) = (n, k) := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    rfl
  | succ m ih =>
    induction k with
    | zero =>
      have h2 : (m + 1) * (m + 1 + 1) / 2 = m * (m + 1) / 2 + m + 1 := by
        have : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by ring
        rw [this, Nat.add_mul_div_left _ _ (by norm_num)]
        ring
      rw [h2, Nat.add_zero, pos_succ, ih m le_rfl]
      simp
    | succ k ihk =>
      rw [← Nat.add_assoc, pos_succ, ihk (by omega)]
      simp only
      rw [if_pos (by omega)]

/-! ### `Minv` is the inverse of `M` -/

theorem invRows_length (n : ℕ) : (invRows n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [invRows, ih]

theorem invRows_getD (n j : ℕ) :
    (invRows n).getD j [] = if j < n then nextRow (invRows j) else [] := by
  induction n with
  | zero => simp [invRows]
  | succ n ih =>
    rw [invRows]
    rcases lt_trichotomy j n with h | h | h
    · rw [List.getD_append _ _ _ _ (by rw [invRows_length]; exact h), ih, if_pos h,
        if_pos (by omega)]
    · subst h
      rw [List.getD_append_right _ _ _ _ (by rw [invRows_length]), invRows_length,
        Nat.sub_self, if_pos (by omega)]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by rw [invRows_length]; omega), invRows_length,
        if_neg (by omega)]
      obtain ⟨d, hd⟩ : ∃ d, j - n = d + 1 := ⟨j - n - 1, by omega⟩
      rw [hd]
      rfl

theorem Minv_eq (n k : ℕ) : Minv n k = (nextRow (invRows n)).getD k 0 := by
  rw [Minv, invRows_getD, if_pos (Nat.lt_succ_self n)]

/-- `N` is lower triangular. -/
theorem Minv_eq_zero (n k : ℕ) (h : n < k) : Minv n k = 0 := by
  rw [Minv_eq]
  exact List.getD_eq_default _ _ (by simp [nextRow, invRows_length]; omega)

/-- Forward substitution: `N(n,k) = [k = n] - ∑_{j<n} M(n,j) N(j,k)` for `k ≤ n`. -/
theorem Minv_rec (n k : ℕ) (hk : k ≤ n) :
    Minv n k = (if k = n then 1 else 0) - ∑ j ∈ range n, M n j * Minv j k := by
  rw [Minv_eq, nextRow, List.getD_eq_getElem _ _ (by simp [invRows_length]; omega),
    List.getElem_map, List.getElem_range, invRows_length]
  refine congrArg (fun s => (if k = n then (1 : ℤ) else 0) - s)
    (Finset.sum_congr rfl fun j hj => ?_)
  rw [invRows_getD, if_pos (Finset.mem_range.mp hj), ← Minv_eq]

theorem M_diag (n : ℕ) : M n n = 1 := by simp [M]

theorem M_eq_zero (n j : ℕ) (h : n < j) : M n j = 0 := by
  rw [M, if_neg (by omega)]

/-- Row `n` of `M · N` is row `n` of the identity, as a finite sum over any range `L > n`. -/
theorem sum_M_mul_Minv (L n k : ℕ) (hn : n < L) :
    ∑ j ∈ range L, M n j * Minv j k = if n = k then 1 else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = n + 1 + m := ⟨L - (n + 1), by omega⟩
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := range m)
    (fun x _ => by rw [M_eq_zero _ _ (by omega), zero_mul]), add_zero, Finset.sum_range_succ,
    M_diag, one_mul]
  by_cases hk : k ≤ n
  · rw [Minv_rec n k hk]
    by_cases h : k = n
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  · rw [Minv_eq_zero _ _ (by omega), if_neg (by omega),
      Finset.sum_eq_zero (fun j hj => by
        rw [Minv_eq_zero _ _ (by have := Finset.mem_range.mp hj; omega), mul_zero])]
    ring

/-! ### `T` is `M^(-2)` -/

/-- The `L × L` truncation of the triangle `M` (A061554). -/
def Mmat (L : ℕ) : Matrix (Fin L) (Fin L) ℚ := Matrix.of fun i j => (M i j : ℚ)

/-- The `L × L` truncation of `N = Minv`. -/
def Nmat (L : ℕ) : Matrix (Fin L) (Fin L) ℚ := Matrix.of fun i j => (Minv i j : ℚ)

/-- The `L × L` truncation of the triangle `T`. -/
def Tmat (L : ℕ) : Matrix (Fin L) (Fin L) ℚ := Matrix.of fun i j => (T i j : ℚ)

theorem Mmat_mul_Nmat (L : ℕ) : Mmat L * Nmat L = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Mmat, Nmat, Matrix.of_apply, Matrix.one_apply]
  rw [Fin.sum_univ_eq_sum_range (fun x => (M i x : ℚ) * (Minv x k : ℚ)) L]
  have h := congrArg (fun z : ℤ => (z : ℚ)) (sum_M_mul_Minv L i k i.isLt)
  simp only [Int.cast_sum, Int.cast_mul] at h
  rw [h]
  by_cases hik : i = k
  · rw [if_pos hik, if_pos (congrArg Fin.val hik)]; rfl
  · rw [if_neg hik, if_neg (fun h' => hik (Fin.ext h'))]; rfl

/-- `Minv` is the inverse of `M`: for every `L`, the `L × L` truncation of `Minv` is the
(Mathlib) inverse of the `L × L` truncation of `M`. -/
theorem Nmat_eq_inv (L : ℕ) : Nmat L = (Mmat L)⁻¹ :=
  (Matrix.inv_eq_right_inv (Mmat_mul_Nmat L)).symm

/-- `T` is lower triangular. -/
theorem T_eq_zero (n k : ℕ) (h : n < k) : T n k = 0 :=
  Finset.sum_eq_zero fun j hj => by
    rw [Minv_eq_zero j k (by have := Finset.mem_range.mp hj; omega), mul_zero]

/-- Row `n` of `N · N` is row `n` of `T`, as a finite sum over any range `L > n`. -/
theorem sum_Minv_mul_Minv (L n k : ℕ) (hn : n < L) :
    ∑ j ∈ range L, Minv n j * Minv j k = T n k := by
  obtain ⟨m, rfl⟩ : ∃ m, L = n + 1 + m := ⟨L - (n + 1), by omega⟩
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := range m)
    (fun x _ => by rw [Minv_eq_zero n _ (by omega), zero_mul]), add_zero, T]

theorem Tmat_eq (L : ℕ) : Tmat L = Nmat L * Nmat L := by
  ext i k
  simp only [Matrix.mul_apply, Tmat, Nmat, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun x => (Minv i x : ℚ) * (Minv x k : ℚ)) L,
    ← sum_Minv_mul_Minv L i k i.isLt]
  push_cast
  rfl

/-- `T = M^(-2)`: for every `L`, the `L × L` truncation of `T` is the `-2`-nd power (in
Mathlib's sense) of the `L × L` truncation of `M`. -/
theorem T_spec (L : ℕ) : Tmat L = Mmat L ^ (-2 : ℤ) := by
  rw [Tmat_eq, Nmat_eq_inv, ← sq, Matrix.inv_pow', ← Matrix.zpow_neg_natCast]
  rfl

/-! ### The conjecture -/

open MvPowerSeries

/-- The bivariate generating function of the triangle,
`∑_{n ≥ 0} ∑_{k=0}^{n} T(n,k) x^n y^k` with `x = X 0` and `y = X 1`: the coefficient of
`x^n y^k` is `T(n,k)` if `k ≤ n` and `0` otherwise. -/
noncomputable def gf : MvPowerSeries (Fin 2) ℚ :=
  fun m => if m 1 ≤ m 0 then (T (m 0) (m 1) : ℚ) else 0

/-- The coefficient of `x^n y^k` in `gf` is `T(n,k)` for `k ≤ n` (and `0` for `k > n`). -/
theorem coeff_gf (n k : ℕ) :
    coeff (Finsupp.single 0 n + Finsupp.single 1 k) gf = if k ≤ n then (T n k : ℚ) else 0 := by
  show (if _ then _ else _) = _
  simp

/-- The conjectured g.f. of A126127 as a triangle:
`∑_{n,k} T(n,k) x^n y^k = (1-x)(1-x+x^2)/(1-xy+3x^2-x^3y+x^4)`, as an identity of formal power
series in `x = X 0` and `y = X 1` over `ℚ`. -/
def statement : Prop :=
  gf = (1 - X 0) * (1 - X 0 + X 0 ^ 2) *
    (1 - X 0 * X 1 + 3 * X 0 ^ 2 - X 0 ^ 3 * X 1 + X 0 ^ 4 : MvPowerSeries (Fin 2) ℚ)⁻¹

/-- The denominator `1 - xy + 3x^2 - x^3y + x^4`. -/
noncomputable def den : MvPowerSeries (Fin 2) ℚ :=
  1 - X 0 * X 1 + 3 * X 0 ^ 2 - X 0 ^ 3 * X 1 + X 0 ^ 4

theorem constantCoeff_den : constantCoeff den = 1 := by
  simp [den]

/-- The conjecture with the denominator cleared. -/
theorem statement_iff : statement ↔ gf * den = (1 - X 0) * (1 - X 0 + X 0 ^ 2) :=
  MvPowerSeries.eq_mul_inv_iff_mul_eq (by simp)

end Math0.Statements.A126127
