/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A281000: Schulte's conjectures on the triangle `C(2n+1,2k+1)·Cat(n-k)`

Source: https://oeis.org/A281000, Werner Schulte, Jan 12 2017 (FORMULA section). Verbatim:
> Conjectures:
>   (1) Antidiagonal sums equal A001003(n+1);
>   (2) Sum_{k=0..n} (-1)^k*T(n,k)*(2*k+1)*A000108(k)*A103365(k) = A000007(n);
>   (3) Matrix inverse equals T(n,k)*A103365(n+1-k).

The entry (offset `0`, keyword `tabl`) is "Triangle read by rows:
T(n,k) = binomial(2*n+1, 2*k+1)*binomial(2*n-2*k, n-k)/(n+1-k) for 0 <= k <= n."

## Encoding

* *The triangle.* `T n k` is the displayed formula, computed in `ℕ`. The division is exact
  (`binomial(2m, m)` is divisible by `m + 1`: it is `(m+1)·Cat(m)`). For `k > n` the formula gives
  `0` (since `binomial(2n+1, 2k+1) = 0`), i.e. `T` is extended by zeros above the diagonal, as
  usual for a lower-triangular matrix. `a` is the triangle read by rows (the OEIS sequence itself,
  offset `0`); `a_data` checks all 55 listed terms (rows `0, …, 9`) in the kernel.
* *A001003* (little Schröder numbers, offset `0`: `1, 1, 3, 11, 45, …`). We use the classical
  Narayana-sum formula from the entry (Cloitre; "row sums of A001263 * [1, 2, 4, 8, …]"):
  `A001003(0) = 1` and `A001003(n) = Σ_{j=1..n} 2^(j-1)·N(n,j)` for `n ≥ 1`, where
  `N(n,j) = C(n-1,j-1)·C(n,j-1)/j` is the Narayana triangle A001263 (its OEIS definition).
  `A001003_data` checks all 26 listed terms.
* *A103365* (offset `1`): "First column of triangle A103364, which equals the matrix inverse of
  the Narayana triangle (A001263)". The Narayana triangle `N(n,j)` (`1 ≤ j ≤ n`) is
  lower unitriangular, so the first column `b` of its inverse is the unique solution of
  `Σ_{j=1..n} N(n,j)·b(j) = [n = 1]` for all `n ≥ 1`; we compute it by forward substitution,
  `b(n) = [n = 1] - Σ_{j=1..n-1} N(n,j)·b(j)` (`invNarayanaCol`). `A103365 0 = 0` is a junk
  value outside the offset (it is only ever multiplied by `T(n,k) = 0`, see below).
  `A103365_data` checks all 20 listed terms `a(1), …, a(20)`.
* *A000108* is Mathlib's `catalan`, and *A000007(n)* is `0 ^ n` (`= 1` for `n = 0`, else `0`).

## The three conjectures

* `conj1` (antidiagonal sums): for every `n ≥ 0`, `Σ_{k=0..⌊n/2⌋} T(n-k,k) = A001003(n+1)`.
  The `n`-th antidiagonal consists of the entries `T(i,j)` with `i + j = n`; those with
  `j > i` lie outside the triangle, so the sum runs over `k = j ≤ ⌊n/2⌋`. (Index `n` of the sum
  matches `A001003(n+1)`: `1 = A001003(1)`, `3 = A001003(2)`, `10 + 1 = A001003(3)`, ….)
* `conj3` (matrix inverse): the infinite lower-triangular matrix `T` has inverse
  `U(n,k) = T(n,k)·A103365(n+1-k)`. Both matrices are lower triangular (for `k > n`,
  `U(n,k) = 0` because `T(n,k) = 0`, whatever the natural-number subtraction `n+1-k` gives), so
  this is equivalent to: for every `N`, the inverse of the `N × N` leading principal submatrix of
  `T` is the `N × N` leading principal submatrix of `U`. We state it in that form over `ℚ`,
  using Mathlib's matrix inverse `⁻¹`.
* `conj2` (reading choice). As written, (2) is not well defined: at `k = 0` it uses
  `A103365(0)`, but A103365 has offset `1` (its first term is `A103365(1) = 1`). With only the
  index shift `A103365(k) ↦ A103365(k+1)` it is false already at `n = 1` (the sum is
  `3 + 3 = 6`), because the factor `(-1)^k` cancels the alternating signs of A103365. The
  identity the author presumably meant is the `k = 0` column of (3) (`T · T⁻¹ = I`, with
  `T⁻¹(k,0) = T(k,0)·A103365(k+1) = (2k+1)·Cat(k)·A103365(k+1)`). We therefore read the factor
  `(-1)^k·A103365(k)` as `A103365(k+1)`: A103365 indexed from `0`, with its sign pattern
  `(-1)^k` absorbed (for the listed terms this is the same as reading `A103365(k)` as the
  `k`-th term, counted from `0`, of the unsigned sequence `|A103365|`). This is the convention of
  P. D. Hanna's g.f. in the A103365 entry itself: `A(x) = Σ_{n≥0} (-1)^n·a(n)·x^n/[n!(n+1)!/2^n]
  = 1 - x + 2x^2/3 - 7x^3/18 + …`, where `(-1)^n·a(n)` is `A103365(n+1)`. So `conj2` states
  `Σ_{k=0..n} T(n,k)·(2k+1)·A000108(k)·A103365(k+1) = A000007(n)` for every `n ≥ 0`.
  It is the `k = 0` column of `conj3`, so including it does not change the strength of
  `statement`.
* `statement := conj1 ∧ conj2 ∧ conj3`.

`conj1_check`, `conj2_check` and `conj3_check` confirm the identities for small `n` (sanity
checks of the transcription, not proofs; `conj3_check` checks the entries of the matrix product
`T · U` in `ℤ`).
-/

namespace Math0.Statements.A281000

/-! ### The triangle -/

/-- A281000: `T(n,k) = binomial(2n+1, 2k+1)·binomial(2n-2k, n-k)/(n+1-k)` for `0 ≤ k ≤ n`
(and `0` for `k > n`). -/
def T (n k : ℕ) : ℕ :=
  Nat.choose (2 * n + 1) (2 * k + 1) * Nat.choose (2 * n - 2 * k) (n - k) / (n + 1 - k)

/-- A281000 as a sequence (offset `0`): the triangle `T` read by rows. (Rows `0, …, i` contain at
least `i + 1` entries, so the `i`-th entry of the concatenation lies among them.) -/
def a (i : ℕ) : ℕ :=
  ((List.range (i + 1)).flatMap fun n => (List.range (n + 1)).map (T n)).getD i 0

/-- The definition reproduces all 55 terms listed in OEIS, `a 0, …, a 54` (kernel-checked). -/
theorem a_data : (List.range 55).map (fun i => a (i + 0)) =
    [1, 3, 1, 10, 10, 1, 35, 70, 21, 1, 126, 420, 252, 36, 1, 462, 2310, 2310, 660, 55, 1,
      1716, 12012, 18018, 8580, 1430, 78, 1, 6435, 60060, 126126, 90090, 25025, 2730,
      105, 1, 24310, 291720, 816816, 816816, 340340, 61880, 4760, 136, 1, 92378, 1385670,
      4988412, 6651216, 3879876, 1058148, 135660, 7752, 171, 1] := by
  decide +kernel

/-! ### Auxiliary sequences -/

/-- The Narayana triangle A001263: `N(n,k) = C(n-1,k-1)·C(n,k-1)/k` for `1 ≤ k ≤ n`. -/
def narayana (n k : ℕ) : ℕ :=
  Nat.choose (n - 1) (k - 1) * Nat.choose n (k - 1) / k

/-- A001003 (little Schröder numbers, offset `0`): `A001003(0) = 1` and
`A001003(n) = Σ_{j=1..n} 2^(j-1)·N(n,j)` for `n ≥ 1`. -/
def A001003 (n : ℕ) : ℕ :=
  if n = 0 then 1 else ∑ j ∈ Finset.Icc 1 n, 2 ^ (j - 1) * narayana n j

/-- All 26 listed terms of A001003, `A001003 0, …, A001003 25` (kernel-checked). -/
theorem A001003_data : (List.range 26).map A001003 =
    [1, 1, 3, 11, 45, 197, 903, 4279, 20793, 103049, 518859, 2646723, 13648869, 71039373,
      372693519, 1968801519, 10463578353, 55909013009, 300159426963, 1618362158587,
      8759309660445, 47574827600981, 259215937709463, 1416461675464871,
      7760733824437545, 42624971294485657] := by
  decide +kernel

/-- `invNarayanaCol m = [b 1, …, b m]`: the first `m` entries of the first column `b` of the
inverse of the (lower unitriangular) Narayana triangle, by forward substitution:
`b(n) = [n = 1] - Σ_{j=1..n-1} N(n,j)·b(j)` (row `n` of `N · b = e₁`, using `N(n,n) = 1`). -/
def invNarayanaCol : ℕ → List ℤ
  | 0 => []
  | m + 1 =>
    let l := invNarayanaCol m
    l ++ [(if m = 0 then 1 else 0) -
      ((List.range m).map fun j => (narayana (m + 1) (j + 1) : ℤ) * l.getD j 0).sum]

/-- A103365 (offset `1`): first column of the matrix inverse of the Narayana triangle A001263.
(`A103365 0 = 0` is a junk value outside the offset.) -/
def A103365 (n : ℕ) : ℤ :=
  (invNarayanaCol n).getD (n - 1) 0

/-- All 20 listed terms of A103365, `A103365 1, …, A103365 20` (kernel-checked). -/
theorem A103365_data : (List.range 20).map (fun i => A103365 (i + 1)) =
    [1, -1, 2, -7, 39, -321, 3681, -56197, 1102571, -27036487, 810263398, -29139230033,
      1238451463261, -61408179368043, 3513348386222286, -229724924077987509,
      17023649385410772579, -1419220037471837658603, 132236541042728184852942,
      -13690229149108218523467549] := by
  decide +kernel

/-! ### The conjectures -/

/-- Conjecture (1): the antidiagonal sums of `T` are the little Schröder numbers:
`Σ_{k=0..⌊n/2⌋} T(n-k,k) = A001003(n+1)` for every `n ≥ 0`. -/
def conj1 : Prop :=
  ∀ n : ℕ, ∑ k ∈ Finset.range (n / 2 + 1), T (n - k) k = A001003 (n + 1)

/-- Conjecture (2), in the corrected reading explained in the module docstring:
`Σ_{k=0..n} T(n,k)·(2k+1)·Cat(k)·A103365(k+1) = A000007(n) = 0^n` for every `n ≥ 0`. -/
def conj2 : Prop :=
  ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1),
    (T n k : ℤ) * (2 * k + 1) * (catalan k : ℤ) * A103365 (k + 1) = (0 : ℤ) ^ n

/-- Conjecture (3): the matrix inverse of `T` is `U(n,k) = T(n,k)·A103365(n+1-k)`; stated for
every leading principal `N × N` submatrix (both matrices are lower triangular). -/
def conj3 : Prop :=
  ∀ N : ℕ, (Matrix.of fun i j : Fin N => (T i j : ℚ))⁻¹ =
    Matrix.of fun i j : Fin N => (T i j : ℚ) * (A103365 ((i : ℕ) + 1 - (j : ℕ)) : ℚ)

/-- Werner Schulte's conjectures (1), (2), (3) on A281000 (Jan 12 2017). -/
def statement : Prop :=
  conj1 ∧ conj2 ∧ conj3

/-! ### Sanity checks of the transcription (not proofs) -/

/-- Conjecture (1) holds for `n ≤ 24`. -/
theorem conj1_check :
    ∀ n < 25, ∑ k ∈ Finset.range (n / 2 + 1), T (n - k) k = A001003 (n + 1) := by
  decide +kernel

/-- Conjecture (2) (corrected reading) holds for `n ≤ 15`. -/
theorem conj2_check : ∀ n < 16, ∑ k ∈ Finset.range (n + 1),
    (T n k : ℤ) * (2 * k + 1) * (catalan k : ℤ) * A103365 (k + 1) = (0 : ℤ) ^ n := by
  simp only [catalan_eq_centralBinom_div]
  decide +kernel

/-- The entries of `T · U` for `n, k ≤ 14` are those of the identity matrix
(`U(j,k) = T(j,k)·A103365(j+1-k)`). -/
theorem conj3_check : ∀ n < 15, ∀ k < 15, ∑ j ∈ Finset.range (n + 1),
    (T n j : ℤ) * ((T j k : ℤ) * A103365 (j + 1 - k)) = if n = k then 1 else 0 := by
  decide +kernel

end Math0.Statements.A281000
