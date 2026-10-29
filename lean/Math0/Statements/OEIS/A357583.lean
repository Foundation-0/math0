/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A357583: Kurkov's recursion for the row polynomials of convolution triangles

Source: https://oeis.org/A357583, Mikhail Kurkov, Apr 05 2025 (FORMULA section). Verbatim:
> Conjecture: row polynomials are x*R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) +
> x*R(n-1,1)*R(1,k) for n > 1, k > 0 with R(1,k) = Bell(k) for k > 0. The same recursion seems
> to work for self-convolution of any other sequence.

The entry (Peter Luschny, Oct 05 2022; offset `0`, keyword `tabl`) is "Triangle read by rows.
Convolution triangle of the Bell numbers." It is computed as `PMatrix(10, combinat[bell])` with
the Maple procedure `PMatrix` of A357368, whose comments fix the terminology: the convolution
triangle of a sequence `a(1), a(2), …` (only the terms with index `≥ 1` are used) is the
`(0,0)`-based lower triangular matrix with `T(0,0) = 1`, `T(n,0) = 0` for `n > 0`, `T(n,1) = a(n)`,
and in general `T(n,k) = [z^n] A(z)^k` with `A(z) = ∑_{j ≥ 1} a(j) z^j`.

## Encoding

* *Convolution triangles.* For a sequence `s : ℕ → R` (`R` a commutative semiring) `pad s` is
  `s` with its value at `0` replaced by `0`, so only `s 1, s 2, …` matter, and `convT s n k` is
  defined by `convT s n 0 = [n = 0]` and
  `convT s n (k+1) = ∑_{i + j = n} pad s i * convT s j k`. `convT_eq_coeff` proves
  `convT s n k = [z^n] (gf s)^k` with `gf s = ∑_{j ≥ 1} s(j) z^j` (a `PowerSeries`). This agrees
  with `PMatrix`: its recursion `T(n,k) = ∑_{i=1}^{n-k+1} a(i) T(n-i,k-1)` (for `2 ≤ k+1 ≤ n`) and
  `T(n,n) = a(1) T(n-1,n-1)` differ from ours only by terms with `T(m,j)`, `j > m`, which vanish;
  the data check below confirms the agreement on all listed terms.
* *Bell numbers.* `Bell(k)` is Mathlib's `Nat.bell k` (`Bell(0) = 1`,
  `Bell(n+1) = ∑_{i ≤ n} C(n,i) Bell(n-i)`, i.e. A000110).
* *The triangle.* `T n k = convT Nat.bell n k` (over `ℕ`). For kernel evaluation `col` computes
  the columns of a convolution triangle as lists (`col_getD`), and `T_eq_Tfast` rewrites `T` to
  that. `T_data` checks all 11 listed rows `n = 0, …, 10` (66 terms). `a` is the triangle read
  by rows (the OEIS sequence itself, offset `0`), and `a_data` checks the 66 listed terms
  `a 0, …, a 65`.
* *Kurkov's polynomials.* For a sequence `s : ℕ → ℤ`, `R s n k : ℤ[X]` (the variable `X` is the
  `x` of the conjecture) is given by `R s 1 k = s(k)` and
  `R s n k = R s (n-1) (k+1) + X * R s (n-1) 1 * R s 1 k` for `n > 1`. The conjecture only
  uses `n ≥ 1, k ≥ 1`; starting from `R s n 1` the recursion only reaches indices `n ≥ 1, k ≥ 1`,
  so the values at `n = 0` (set to `0`) and `k = 0` (given by the same formulas) are never used.
  The Bell instance is `R bellZ`, `bellZ k = Bell(k)` as an integer.
* *Row polynomials.* The row polynomial of row `n` of the convolution triangle of `s` is
  `rowPoly s n = ∑_{k=0}^{n} convT s n k * X^k`.
* *The conjecture.* `statement` is the conjunction of its two sentences:
  1. for every `n > 0`, `∑_{k=0}^{n} T(n,k) X^k = X * R bellZ n 1` in `ℤ[X]`;
  2. for every integer sequence `s` (only `s(k)` for `k ≥ 1` matter) and every `n > 0`,
     `rowPoly s n = X * R s n 1` in `ℤ[X]` ("the same recursion" with `R(1,k) = s(k)` for the
     convolution triangle of `s`). We read "any other sequence" as any integer sequence, as
     OEIS sequences are integer sequences.
-/

namespace Math0.Statements.A357583

open Polynomial

/-! ### Convolution triangles -/

section ConvolutionTriangle

variable {R : Type*} [CommSemiring R]

/-- The sequence `s` with its value at `0` replaced by `0`: a convolution triangle only uses
`s 1, s 2, …`. -/
def pad (s : ℕ → R) (j : ℕ) : R := if j = 0 then 0 else s j

/-- The convolution triangle of the sequence `s(1), s(2), …` (A357368's `PMatrix`):
`convT s n k = [z^n] (∑_{j ≥ 1} s(j) z^j)^k` (see `convT_eq_coeff`). -/
def convT (s : ℕ → R) : ℕ → ℕ → R
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, pad s p.1 * convT s p.2 k

/-- The generating function `∑_{j ≥ 1} s(j) z^j` of the sequence `s(1), s(2), …`. -/
noncomputable def gf (s : ℕ → R) : PowerSeries R := PowerSeries.mk (pad s)

/-- The convolution triangle as coefficients of powers of the generating function:
`T(n,k) = [z^n] (∑_{j ≥ 1} s(j) z^j)^k`. -/
theorem convT_eq_coeff (s : ℕ → R) (n k : ℕ) :
    convT s n k = PowerSeries.coeff n (gf s ^ k) := by
  induction k generalizing n with
  | zero => simp [convT, PowerSeries.coeff_one]
  | succ k ih =>
    rw [pow_succ', PowerSeries.coeff_mul, convT]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ih, gf, PowerSeries.coeff_mk]

/-- The columns `0, 1, …` of the convolution triangle of `s`, each as the list of its first `N`
entries (for fast evaluation). -/
def col (s : ℕ → R) (N : ℕ) : ℕ → List R
  | 0 => (List.range N).map (fun n => if n = 0 then 1 else 0)
  | k + 1 => (List.range N).map (fun n =>
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, pad s p.1 * (col s N k).getD p.2 0)

theorem col_getD (s : ℕ → R) (N k n : ℕ) (hn : n < N) :
    (col s N k).getD n 0 = convT s n k := by
  induction k generalizing n with
  | zero => simp [col, convT, List.getD_eq_getElem?_getD, List.getElem?_range hn]
  | succ k ih =>
    simp only [col, convT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn,
      Option.map_some, Option.getD_some]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [← ih p.2 (by omega), List.getD_eq_getElem?_getD]

end ConvolutionTriangle

/-! ### The triangle A357583 -/

/-- A357583: `T(n, k)` is the convolution triangle of the Bell numbers,
`T(n,k) = [z^n] (∑_{j ≥ 1} Bell(j) z^j)^k`. -/
def T (n k : ℕ) : ℕ := convT Nat.bell n k

/-- Fast evaluation of `T n k` via the column lists. -/
def Tfast (n k : ℕ) : ℕ := (col Nat.bell (n + 1) k).getD n 0

theorem T_eq_Tfast (n k : ℕ) : T n k = Tfast n k :=
  (col_getD Nat.bell (n + 1) k n (Nat.lt_succ_self n)).symm

/-- The definition reproduces the 11 listed rows `n = 0, …, 10` of the triangle
(kernel-checked). -/
theorem T_data : (List.range 11).map (fun n => (List.range (n + 1)).map (T n)) =
    [[1],
     [0, 1],
     [0, 2, 1],
     [0, 5, 4, 1],
     [0, 15, 14, 6, 1],
     [0, 52, 50, 27, 8, 1],
     [0, 203, 189, 113, 44, 10, 1],
     [0, 877, 764, 471, 212, 65, 12, 1],
     [0, 4140, 3311, 2013, 974, 355, 90, 14, 1],
     [0, 21147, 15378, 8951, 4440, 1790, 550, 119, 16, 1],
     [0, 115975, 76418, 41745, 20526, 8727, 3027, 805, 152, 18, 1]] := by
  rw [funext₂ T_eq_Tfast]
  decide +kernel

/-- A357583 as a sequence (offset `0`): the triangle `T` read by rows. (Rows `0, …, i` contain at
least `i + 1` entries, so the `i`-th entry of the concatenation lies among them.) -/
def a (i : ℕ) : ℕ :=
  ((List.range (i + 1)).flatMap fun n => (List.range (n + 1)).map (T n)).getD i 0

/-- The definition reproduces all 66 terms listed in OEIS, `a 0, …, a 65` (kernel-checked). -/
theorem a_data : (List.range 66).map (fun i => a (i + 0)) =
    [1, 0, 1, 0, 2, 1, 0, 5, 4, 1, 0, 15, 14, 6, 1, 0, 52, 50, 27, 8, 1, 0, 203, 189, 113, 44,
      10, 1, 0, 877, 764, 471, 212, 65, 12, 1, 0, 4140, 3311, 2013, 974, 355, 90, 14, 1, 0,
      21147, 15378, 8951, 4440, 1790, 550, 119, 16, 1, 0, 115975, 76418, 41745, 20526, 8727,
      3027, 805, 152, 18, 1] := by
  unfold a
  rw [funext₂ T_eq_Tfast]
  decide +kernel

/-! ### Kurkov's recursion -/

/-- Kurkov's polynomials for the sequence `s`: `R(1,k) = s(k)` and
`R(n,k) = R(n-1,k+1) + x * R(n-1,1) * R(1,k)` for `n > 1` (only `n, k ≥ 1` are meaningful;
`R s 0 k = 0` is a junk value). -/
noncomputable def R (s : ℕ → ℤ) : ℕ → ℕ → ℤ[X]
  | 0, _ => 0
  | 1, k => C (s k)
  | n + 2, k => R s (n + 1) (k + 1) + X * R s (n + 1) 1 * R s 1 k

/-- The Bell numbers as integers. -/
def bellZ (k : ℕ) : ℤ := (Nat.bell k : ℤ)

/-- The row polynomial `∑_{k=0}^{n} T(n,k) x^k` of row `n` of the convolution triangle of `s`. -/
noncomputable def rowPoly (s : ℕ → ℤ) (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (convT s n k) * X ^ k

/-! ### The conjecture -/

/-- Conjecture (Mikhail Kurkov, 2025): (1) for every `n > 0`, the row polynomial
`∑_{k=0}^{n} T(n,k) x^k` of A357583 equals `x * R(n,1)`, where `R(1,k) = Bell(k)` and
`R(n,k) = R(n-1,k+1) + x * R(n-1,1) * R(1,k)` for `n > 1`, `k > 0`; and (2) the same holds for
the convolution triangle of any (integer) sequence `s(1), s(2), …`, with `R(1,k) = s(k)`. -/
def statement : Prop :=
  (∀ n : ℕ, 0 < n →
      ∑ k ∈ Finset.range (n + 1), C (T n k : ℤ) * X ^ k = X * R bellZ n 1) ∧
  (∀ s : ℕ → ℤ, ∀ n : ℕ, 0 < n → rowPoly s n = X * R s n 1)

end Math0.Statements.A357583
