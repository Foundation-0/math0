/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A141412: denominators of the coefficients of Curtz's polynomials `P(n,x)`

Source: https://oeis.org/A141412, _Michel Marcus_, Oct 18 2018 (FORMULA section). Verbatim:
> Conjecture: T(n, k) = d(n+1, k+1), with d(n,k) = denominator(A000254(n, k)*k!/n!) where
> A000254 are the unsigned Stirling numbers of the 1st kind. See d(n,k) in Farhi link.

The entry (_Paul Curtz_, Aug 04 2008, offset `0`, keyword `tabl`) is "Triangle c(n,k) of the
denominators of coefficients [x^k] P(n,x) of the polynomials P(n,x) of A129891", read by rows
`0 ≤ k ≤ n`. The polynomials are defined in A129891 / A140749: "P(0,x)=1 and
P(n,x) = (-1)^n/(n+1) + x* Sum_{i=0..n-1} (-1)^i*P(n-1-i,x)/(i+1)".

## Encoding

* `P n : ℚ[X]` is the polynomial `P(n,x)`, defined literally by that recursion (written for
  `n + 1`: `P(n+1,x) = (-1)^(n+1)/((n+1)+1) + x ∑_{i=0}^{n} (-1)^i/(i+1) P(n-i,x)`). It is
  noncomputable (Mathlib polynomials are), so the table entries are computed by `c n k : ℚ`, a
  computable recursion for the coefficients, and `coeff_P` proves `(P n).coeff k = c n k` for all
  `n, k`.
* `T n k = (c n k).den` is the denominator of `[x^k] P(n,x)` (`T_eq_den_coeff`); Mathlib's `Rat`
  is in lowest terms with positive denominator, as Maple's `denom` / Mathematica's `Denominator`
  in the entry's programs. `T_data` checks all 78 listed terms (rows `n = 0, …, 11`, read by
  rows) in the kernel. (The triangle is named `T`, as in the conjecture, rather than `a`.)
* `d n k = den(|s(n,k)| · k!/n!)`. Although A000254 is, strictly, the one-index sequence
  `|s(n+1,2)|`, the comment uses it as a two-argument function and explicitly says it means "the
  unsigned Stirling numbers of the 1st kind", so `A000254(n, k)` is read as the unsigned Stirling
  number of the first kind `|s(n,k)|`, Mathlib's `Nat.stirlingFirst n k` (= A132393(n,k)). This
  agrees with Farhi's `d(n,k)` and with G. C. Greubel's formula/programs in the entry
  (`Denominator[(k+1)!*StirlingS1[n+1,k+1]/(n+1)!]`; the sign does not affect the denominator).
* *The conjecture.* `statement`: for every entry of the triangle, i.e. all `n ≥ 0` and
  `0 ≤ k ≤ n`, `T n k = d (n+1) (k+1)`.
-/

namespace Math0.Statements.A141412

open Polynomial

/-- Curtz's polynomials (A129891, A140749): `P(0,x) = 1` and, for `n ≥ 1`,
`P(n,x) = (-1)^n/(n+1) + x ∑_{i=0}^{n-1} (-1)^i/(i+1) · P(n-1-i,x)` (written here for `n + 1`). -/
noncomputable def P : ℕ → ℚ[X]
  | 0 => 1
  | n + 1 => C ((-1) ^ (n + 1) / (((n + 1 : ℕ) : ℚ) + 1)) +
      X * ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i / ((i : ℚ) + 1)) * P (n - i)
decreasing_by omega

/-- The coefficient `[x^k] P(n,x)`, by a computable recursion (see `coeff_P`). -/
def c : ℕ → ℕ → ℚ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (-1) ^ (n + 1) / (((n + 1 : ℕ) : ℚ) + 1)
  | n + 1, k + 1 => ∑ i ∈ Finset.range (n + 1), (-1) ^ i / ((i : ℚ) + 1) * c (n - i) k

/-- `c n k` is the coefficient of `x^k` in `P(n,x)`. -/
theorem coeff_P (n k : ℕ) : (P n).coeff k = c n k := by
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp [P, c]
    | succ n => simp [P, c]
  | succ k ih =>
    cases n with
    | zero => simp [P, c, coeff_one]
    | succ n =>
      rw [P, c, coeff_add, coeff_C, if_neg (Nat.succ_ne_zero k), zero_add, coeff_X_mul,
        finsetSum_coeff]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coeff_C_mul, ih]

/-- A141412: `T(n,k)` is the denominator of the coefficient `[x^k] P(n,x)` (`0 ≤ k ≤ n`). -/
def T (n k : ℕ) : ℕ := (c n k).den

/-- `T(n,k)` is the denominator (in lowest terms) of `[x^k] P(n,x)`. -/
theorem T_eq_den_coeff (n k : ℕ) : T n k = ((P n).coeff k).den := by
  rw [T, coeff_P]

/-- The definition reproduces all 78 terms listed in OEIS (rows `n = 0, …, 11`, read by rows;
kernel-checked). -/
theorem T_data : (List.range 12).flatMap (fun n => (List.range (n + 1)).map (fun k => T n k)) =
    [1, 2, 1, 3, 1, 1, 4, 12, 2, 1, 5, 6, 4, 1, 1, 6, 180, 8, 6, 2, 1, 7, 10, 15, 2, 6, 1, 1, 8,
      560, 240, 240, 6, 4, 2, 1, 9, 1260, 15120, 20, 144, 1, 12, 1, 1, 10, 12600, 672, 945, 32,
      240, 8, 3, 2, 1, 11, 1260, 8400, 1512, 3024, 48, 240, 3, 1, 1, 1, 12, 166320, 100800,
      64800, 12096, 12096, 480, 360, 4, 12, 2, 1] := by
  decide +kernel

/-- Farhi's `d(n,k) = denominator(|s(n,k)| · k!/n!)`, with `|s(n,k)|` the unsigned Stirling
number of the first kind (Mathlib's `Nat.stirlingFirst`). -/
def d (n k : ℕ) : ℕ :=
  ((Nat.stirlingFirst n k : ℚ) * (Nat.factorial k : ℚ) / (Nat.factorial n : ℚ)).den

/-- Conjecture (Marcus, A141412): `T(n,k) = d(n+1,k+1)` for every entry `0 ≤ k ≤ n` of the
triangle. -/
def statement : Prop :=
  ∀ n k : ℕ, k ≤ n → T n k = d (n + 1) (k + 1)

end Math0.Statements.A141412
