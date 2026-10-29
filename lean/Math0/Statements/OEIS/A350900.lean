/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A350900: Schulte's gcd-ratio double sum as a Dirichlet convolution

Source: https://oeis.org/A350900, Werner Schulte, Jan 21 2022 (COMMENTS section). Verbatim:
> Conjecture: Let f be an arbitrary arithmetic function. Define for n > 0 the sequence
> a(f; n) = Sum_{i=1..n, k=1..n} f(gcd(i,n)/gcd(gcd(i,k),n)); a(f; n) equals Dirichlet
> convolution of f(n)*A000010(n) and A057660(n); if f is multiplicative, then a(f; n) is
> multiplicative; row sums of this triangle use f(n) = n (see formula section).

and, in the FORMULA section of the same entry (same author and date). Verbatim:
> Conjecture: Row sums equal Dirichlet convolution of A002618 and A057660.

The entry (keyword `tabl`, offset `1`) is "Triangle read by rows:
T(n, k) = Sum_{i=1..n} gcd(i,n) / gcd(gcd(i,k),n) for 1 <= k <= n."

## Encoding

* *The triangle.* `T n k = ∑_{i=1}^{n} gcd(i,n) / gcd(gcd(i,k),n)` with natural-number division;
  the division is exact, since `gcd(gcd(i,k),n)` divides `gcd(i,n)`. `T_data` checks the 12 rows
  listed in OEIS (`n = 1, …, 12`, i.e. all 78 listed terms) in the kernel.
* *The sequence.* `a` is the triangle read by rows with OEIS offset `1`: `pos i` is the pair
  `(n, k)` in position `i` (0-based) of the row-by-row reading `(1,1), (2,1), (2,2), (3,1), …`
  (rows `1, …, i + 1` contain at least `i + 1` entries, so the position exists), and
  `a (i + 1) = T (pos i).1 (pos i).2`; `a 0 = 0` is outside the offset. `a_data` checks all 78
  listed terms `a 1, …, a 78`.
* *Referenced sequences.* `A000010` is Euler's totient (`Nat.totient`), packaged as the
  arithmetic function `phi`. `A057660 m = ∑_{k=1}^{m} m / gcd(m,k)` is the OEIS definition of
  A057660 (checked against its 52 listed terms in `A057660_data`), packaged as the arithmetic
  function `A057660Fn`. `A002618 n = n * phi(n)` is the OEIS definition of A002618 (its first
  20 terms are checked in `A002618_data`), packaged as `A002618Fn`.
* *Arithmetic functions and Dirichlet convolution.* "Arbitrary arithmetic function" is read as
  a complex-valued function on the positive integers, i.e. Mathlib's `ArithmeticFunction ℂ`
  (a function `ℕ → ℂ` whose value at `0` is `0`; the value at `0` never enters `a(f; n)`, since
  for `1 ≤ i ≤ n` the argument `gcd(i,n)/gcd(gcd(i,k),n)` is `≥ 1`). Dirichlet convolution is
  Mathlib's product `*` of arithmetic functions,
  `(g * h) n = ∑_{d e = n} g d * h e`, the pointwise product `f(n)*A000010(n)` is
  `f.pmul phi`, and ℕ-valued functions are coerced to ℂ-valued ones. "Multiplicative" is
  Mathlib's `ArithmeticFunction.IsMultiplicative` (`g 1 = 1` and `g (m n) = g m g n` for
  coprime `m, n`).
* *`a(f; n)`.* `aF f n = ∑_{i=1}^{n} ∑_{k=1}^{n} f (gcd(i,n) / gcd(gcd(i,k),n))`, for any
  coefficient semiring (the statement uses `ℂ`); it is `0` at `n = 0` (empty sum), so it is
  itself an arithmetic function `aFun f`, which is how "a(f; n) is multiplicative" is read.
* *The conjecture.* `statement` is the conjunction of
  1. for every arithmetic function `f` and every `n > 0`:
     `a(f; n) = ((f · A000010) * A057660)(n)`;
  2. for every multiplicative `f`, `a(f; ·)` is multiplicative;
  3. "row sums of this triangle use f(n) = n": for `n > 0`,
     `∑_{k=1}^{n} T(n,k) = a(id; n)` (with `id` the identity arithmetic function, cast to `ℂ`);
  4. the FORMULA-section conjecture: for `n > 0`,
     `∑_{k=1}^{n} T(n,k) = (A002618 * A057660)(n)` (computed in `ℕ`).
  Parts 1, 3, 4 restrict to `n > 0` as the entry does (at `n = 0` all sides are `0` anyway).
  `statement_check_rows` confirms part 4 for `n ≤ 12`, and `statement_check_aF` confirms the
  identity of part 1 for `n ≤ 12` for one non-multiplicative ℕ-valued test function (sanity
  checks of the transcription, not proofs).
-/

namespace Math0.Statements.A350900

open ArithmeticFunction

/-! ### The triangle and the sequence -/

/-- A350900: `T(n, k) = Sum_{i=1..n} gcd(i,n) / gcd(gcd(i,k),n)`. -/
def T (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, Nat.gcd i n / Nat.gcd (Nat.gcd i k) n

/-- The definition reproduces the 12 rows listed in OEIS (kernel-checked). -/
theorem T_data :
    (List.range 12).map (fun r => (List.range (r + 1)).map (fun j => T (r + 1) (j + 1))) =
    [[1],
     [3, 2],
     [5, 5, 3],
     [8, 5, 8, 4],
     [9, 9, 9, 9, 5],
     [15, 10, 9, 10, 15, 6],
     [13, 13, 13, 13, 13, 13, 7],
     [20, 12, 20, 9, 20, 12, 20, 8],
     [21, 21, 11, 21, 21, 11, 21, 21, 9],
     [27, 18, 27, 18, 15, 18, 27, 18, 27, 10],
     [21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 11],
     [40, 25, 24, 20, 40, 15, 40, 20, 24, 25, 40, 12]] := by
  decide +kernel

/-- The pair `(n, k)` (with `1 ≤ k ≤ n`) in position `i` (0-based) of the triangle read by rows:
`(1,1), (2,1), (2,2), (3,1), …`. Rows `1, …, i + 1` contain at least `i + 1` entries. -/
def pos (i : ℕ) : ℕ × ℕ :=
  ((List.range (i + 1)).flatMap fun r => (List.range (r + 1)).map fun j => (r + 1, j + 1)).getD
    i (0, 0)

/-- A350900 as a sequence (offset `1`): the triangle `T` read by rows. -/
def a : ℕ → ℕ
  | 0 => 0
  | i + 1 => T (pos i).1 (pos i).2

/-- The definition reproduces all 78 terms listed in OEIS, `a 1, …, a 78` (kernel-checked). -/
theorem a_data : (List.range 78).map (fun i => a (i + 1)) =
    [1, 3, 2, 5, 5, 3, 8, 5, 8, 4, 9, 9, 9, 9, 5, 15, 10, 9, 10, 15, 6, 13, 13, 13, 13, 13, 13,
      7, 20, 12, 20, 9, 20, 12, 20, 8, 21, 21, 11, 21, 21, 11, 21, 21, 9, 27, 18, 27, 18, 15,
      18, 27, 18, 27, 10, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 11, 40, 25, 24, 20, 40, 15,
      40, 20, 24, 25, 40, 12] := by
  decide +kernel

/-! ### Referenced sequences as arithmetic functions -/

/-- A000010, Euler's totient, as an arithmetic function. -/
def phi : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

/-- A057660: `a(m) = Sum_{k=1..m} m/gcd(m,k)`. -/
def A057660 (m : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 m, m / Nat.gcd m k

/-- The definition of `A057660` reproduces its 52 listed terms (kernel-checked). -/
theorem A057660_data : (List.range 52).map (fun i => A057660 (i + 1)) =
    [1, 3, 7, 11, 21, 21, 43, 43, 61, 63, 111, 77, 157, 129, 147, 171, 273, 183, 343, 231,
      301, 333, 507, 301, 521, 471, 547, 473, 813, 441, 931, 683, 777, 819, 903, 671, 1333,
      1029, 1099, 903, 1641, 903, 1807, 1221, 1281, 1521, 2163, 1197, 2101, 1563, 1911,
      1727] := by
  decide +kernel

/-- A057660 as an arithmetic function (its value at `0` is the empty sum `0`). -/
def A057660Fn : ArithmeticFunction ℕ := ⟨A057660, by simp [A057660]⟩

/-- A002618: `a(n) = n*phi(n)`. -/
def A002618 (n : ℕ) : ℕ := n * Nat.totient n

/-- The definition of `A002618` reproduces its first 20 listed terms (kernel-checked). -/
theorem A002618_data : (List.range 20).map (fun i => A002618 (i + 1)) =
    [1, 2, 6, 8, 20, 12, 42, 32, 54, 40, 110, 48, 156, 84, 120, 128, 272, 108, 342, 160] := by
  decide +kernel

/-- A002618 as an arithmetic function. -/
def A002618Fn : ArithmeticFunction ℕ := ⟨A002618, by simp [A002618]⟩

/-! ### Schulte's `a(f; n)` -/

/-- `a(f; n) = Sum_{i=1..n, k=1..n} f(gcd(i,n)/gcd(gcd(i,k),n))`. -/
def aF {R : Type*} [AddCommMonoid R] (f : ArithmeticFunction R) (n : ℕ) : R :=
  ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd i n / Nat.gcd (Nat.gcd i k) n)

/-- `a(f; ·)` as an arithmetic function (it vanishes at `0`, an empty sum). -/
def aFun {R : Type*} [AddCommMonoid R] (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨aF f, by simp [aF]⟩

/-! ### The conjecture -/

/-- Conjecture (Werner Schulte, Jan 21 2022): for every arithmetic function `f`,
1. `a(f; n)` equals the Dirichlet convolution of `f(n)*A000010(n)` and `A057660(n)`, for `n > 0`;
2. if `f` is multiplicative, then `a(f; ·)` is multiplicative;
3. the row sums of the triangle are `a(f; n)` for `f(n) = n`, for `n > 0`;

and (FORMULA section) 4. the row sums of the triangle equal the Dirichlet convolution of A002618
and A057660, for `n > 0`. -/
def statement : Prop :=
  (∀ f : ArithmeticFunction ℂ, ∀ n : ℕ, 0 < n →
      aF f n = (f.pmul (phi : ArithmeticFunction ℂ) * (A057660Fn : ArithmeticFunction ℂ)) n) ∧
  (∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (aFun f).IsMultiplicative) ∧
  (∀ n : ℕ, 0 < n →
      ((∑ k ∈ Finset.Icc 1 n, T n k : ℕ) : ℂ) =
        aF ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n) ∧
  (∀ n : ℕ, 0 < n → ∑ k ∈ Finset.Icc 1 n, T n k = (A002618Fn * A057660Fn) n)

/-! ### Sanity checks of the transcription (not proofs) -/

/-- Part 4 of `statement` holds for `n ≤ 12`. -/
theorem statement_check_rows :
    ∀ n < 13, 0 < n → ∑ k ∈ Finset.Icc 1 n, T n k = (A002618Fn * A057660Fn) n := by
  decide +kernel

/-- A non-multiplicative ℕ-valued test function, `f(m) = 2m + (m mod 3)` for `m ≥ 1`. -/
def fTest : ArithmeticFunction ℕ := ⟨fun m => if m = 0 then 0 else 2 * m + m % 3, rfl⟩

/-- The identity of part 1 of `statement`, with `fTest` in place of `f` (computed in `ℕ`), holds
for `n ≤ 12`. -/
theorem statement_check_aF :
    ∀ n < 13, 0 < n → aF fTest n = (fTest.pmul (phi : ArithmeticFunction ℕ) *
      (A057660Fn : ArithmeticFunction ℕ)) n := by
  decide +kernel

end Math0.Statements.A350900
