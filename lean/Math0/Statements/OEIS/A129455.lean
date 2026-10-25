/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A129455: the triple-gcd analog of Pascal's triangle

Source: https://oeis.org/A129455, Peter Bala, Apr 16 2007 (COMMENTS section). Verbatim:
> It appears that the T(n,k) are always integers. This would follow from the conjectured prime
> factorization given in A129454. Calculation suggests that the binomial coefficients C(n,k)
> divide T(n,k) and that T(n,k)/C(n,k) are perfect sixth powers.

The entry (offset `0`, keyword `tabl`) is "An analog of Pascal's triangle based on A129454.
T(n, k) = A129454(n+1)/(A129454(n-k+1)*A129454(k+1))", where A129454 (offset `0`) is
"a(n) = Product{i=1..n-1} Product{j=1..n-1} Product{k=1..n-1} gcd(i,j,k)" (so `a(0) = a(1) = 1`,
the empty product).

## Encoding

* `A129454 n` is the product of `gcd(gcd(i, j), k)` over `i, j, k ∈ [1, n - 1]`, as a `Finset`
  product over `Finset.Icc 1 (n - 1)` (for `n = 0` the range is empty since `0 - 1 = 0` in `ℕ`;
  only arguments `≥ 1` are ever used below). `A129454_data` checks its first 10 listed terms.
* `T n k` (for `0 ≤ k ≤ n`) is `A129454 (n + 1) / (A129454 (n - k + 1) * A129454 (k + 1))`,
  computed with natural-number division. A priori this quotient need not be exact; whether it is
  exact is precisely the first part of the conjecture, which is therefore stated as the
  divisibility `A129454 (n - k + 1) * A129454 (k + 1) ∣ A129454 (n + 1)`. Under that divisibility
  `T n k` is the true (rational) value of `T(n, k)`, and under `C(n,k) ∣ T n k` the natural-number
  quotient `T n k / C(n, k)` is the true value of `T(n,k)/C(n,k)`; so the conjunction below is
  equivalent to the conjecture read over `ℚ`.
* `a` is the triangle read by rows (the OEIS sequence itself, offset `0`); `a_data` checks all 45
  listed terms `a 0, …, a 44` (rows `n = 0, …, 8`) in the kernel.
* The conjecture: for all `n ≥ 0` and `0 ≤ k ≤ n`, (1) `T(n,k)` is an integer, (2) `C(n,k)`
  divides `T(n,k)`, and (3) `T(n,k)/C(n,k) = m^6` for some natural number `m` (a "perfect sixth
  power"; since `T(n,k) > 0`, necessarily `m ≥ 1`). The remark that (1) "would follow from the
  conjectured prime factorization given in A129454" is an explanation, not part of the claim, and
  is not encoded. `statement_check` verifies the three claims for rows `n ≤ 8` with explicit
  sixth roots (a sanity check of the transcription, not a proof).
-/

namespace Math0.Statements.A129455

/-- A129454: `a(n) = ∏_{i=1}^{n-1} ∏_{j=1}^{n-1} ∏_{k=1}^{n-1} gcd(i, j, k)`. -/
def A129454 (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 (n - 1), ∏ j ∈ Finset.Icc 1 (n - 1), ∏ k ∈ Finset.Icc 1 (n - 1),
    Nat.gcd (Nat.gcd i j) k

/-- The definition of A129454 reproduces its first listed terms (kernel-checked). -/
theorem A129454_data : (List.range 10).map A129454 =
    [1, 1, 1, 2, 6, 1536, 7680, 8806025134080, 61642175938560,
      2168841254587541957294161920] := by
  decide +kernel

/-- A129455: `T(n, k) = A129454(n+1)/(A129454(n-k+1)*A129454(k+1))` for `0 ≤ k ≤ n`
(natural-number division). -/
def T (n k : ℕ) : ℕ := A129454 (n + 1) / (A129454 (n - k + 1) * A129454 (k + 1))

/-- A129455 as a sequence (offset `0`): the triangle `T` read by rows. (Rows `0, …, i` contain at
least `i + 1` entries, so the `i`-th entry of the concatenation lies among them.) -/
def a (i : ℕ) : ℕ :=
  ((List.range (i + 1)).flatMap fun n => (List.range (n + 1)).map (T n)).getD i 0

/-- The definition reproduces all 45 terms listed in OEIS, `a 0, …, a 44` (kernel-checked). -/
theorem a_data : (List.range 45).map (fun i => a (i + 0)) =
    [1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 256, 384, 256, 1, 1, 5, 640, 640, 5, 1, 1, 1146617856,
      2866544640, 244611809280, 2866544640, 1146617856, 1, 1, 7, 4013162496, 6688604160,
      6688604160, 4013162496, 7, 1, 1, 35184372088832, 123145302310912,
      47066867504069920948224, 919274755938865643520, 47066867504069920948224,
      123145302310912, 35184372088832, 1] := by
  decide +kernel

/-- Conjecture (Peter Bala, 2007): for all `0 ≤ k ≤ n`, `T(n,k)` is an integer (i.e.
`A129454(n-k+1) * A129454(k+1)` divides `A129454(n+1)`), the binomial coefficient `C(n,k)` divides
`T(n,k)`, and `T(n,k)/C(n,k)` is a perfect sixth power. -/
def statement : Prop :=
  ∀ n k : ℕ, k ≤ n →
    A129454 (n - k + 1) * A129454 (k + 1) ∣ A129454 (n + 1) ∧
    n.choose k ∣ T n k ∧
    ∃ m : ℕ, T n k / n.choose k = m ^ 6

/-- Explicit sixth roots of `T(n,k)/C(n,k)` for rows `n = 0, …, 8`. -/
def roots : List (List ℕ) :=
  [[1],
   [1, 1],
   [1, 1, 1],
   [1, 1, 1, 1],
   [1, 2, 2, 2, 1],
   [1, 1, 2, 2, 1, 1],
   [1, 24, 24, 48, 24, 24, 1],
   [1, 1, 24, 24, 24, 24, 1, 1],
   [1, 128, 128, 3072, 1536, 3072, 128, 128, 1]]

/-- Sanity check of the transcription (not a proof): the three claims hold for rows `n ≤ 8`,
with the sixth roots listed in `roots`. -/
theorem statement_check : ∀ n < 9, ∀ k < n + 1,
    A129454 (n - k + 1) * A129454 (k + 1) ∣ A129454 (n + 1) ∧
    n.choose k ∣ T n k ∧
    T n k / n.choose k = ((roots.getD n []).getD k 0) ^ 6 := by
  decide +kernel

end Math0.Statements.A129455
