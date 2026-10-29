/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A328202: gcd of the interior binomial coefficients of row `n`

Source: https://oeis.org/A328202, _Jon Maiga_, Oct 08 2019 (FORMULA section). Verbatim:
> a(n) = A014963(n) * A014963(n - 1) (conjecture). - _Jon Maiga_, Oct 08 2019

The entry (by _Joel Kaufmann_, Oct 07 2019) is named "a(n) is the greatest common divisor of
all the numbers in row n of Pascal's triangle excluding 1 and n.", with offset `4`. Its listed
data are `a(4), …, a(78)`.

The same entry also contains, in the COMMENTS, a second conjecture (from _Robert Israel_,
Oct 16 2019):
> If p is a Fermat prime > 3, a(p)=2*p.
> If p is a Mersenne prime, a(p+1)=2*p.
> Conjecture: these are the only cases where a(n)>n.

It is recorded below as `statementIsrael`; the main target of this file is `statement`.

## Encoding

* *The sequence.* Row `n` of Pascal's triangle is `C(n, 0), C(n, 1), …, C(n, n)`. Excluding
  the entries `1` and `n` means dropping `C(n, 0) = C(n, n) = 1` and `C(n, 1) = C(n, n-1) = n`;
  for `n ≥ 4` every remaining entry `C(n, k)`, `2 ≤ k ≤ n - 2`, is `> n`, so nothing else is
  dropped. Hence `a n = gcd {C(n, k) : 2 ≤ k ≤ n - 2}`, written as
  `(Finset.Icc 2 (n - 2)).gcd (Nat.choose n)`. (This matches the entry's programs, which take the
  gcd over `2 ≤ k ≤ n/2`, a set with the same values by `C(n, k) = C(n, n - k)`.) The value of
  `a n` for `n < 4` is irrelevant: the offset is `4` and every statement below assumes `n ≥ 4`.
  `a_data` kernel-checks all `75` listed terms `a(4), …, a(78)`.
* *A014963.* Its name: "Exponential of Mangoldt function M(n): a(n) = 1 unless n is a prime or
  prime power, in which case a(n) = that prime." (offset `1`). `expMangoldt m` is `m.minFac`
  (the prime `p`) when `IsPrimePow m` (i.e. `m = p ^ k` with `p` prime and `k ≥ 1`), and `1`
  otherwise. `cast_expMangoldt` proves it equals `exp (Λ m)` for Mathlib's von Mangoldt function
  `ArithmeticFunction.vonMangoldt`, and `expMangoldt_data` kernel-checks the `95` listed terms
  `A014963(1), …, A014963(95)`.
* *The conjecture* (`statement`): for every `n ≥ 4`, `a n = expMangoldt n * expMangoldt (n - 1)`.
  Since `n ≥ 4`, `n - 1 ≥ 3` and the natural-number subtraction is exact.
* *Israel's conjecture* (`statementIsrael`, secondary): "these are the only cases where
  a(n) > n" is read as: for every `n ≥ 4` with `a n > n`, either `n` is a Fermat prime `> 3`
  (a prime of the form `2 ^ (2 ^ k) + 1`, `Nat.fermatNumber k`) or `n - 1` is a Mersenne prime
  (a prime of the form `2 ^ m - 1`, `mersenne m`), i.e. `n = p + 1` for a Mersenne prime `p`.
  The two displayed facts (the converse direction) are stated in the entry as facts, not as
  part of the conjecture, so they are not included.
-/

namespace Math0.Statements.A328202

/-- A328202: `a(n)` is the greatest common divisor of all the numbers in row `n` of Pascal's
triangle excluding `1` and `n`, i.e. `gcd {C(n, k) : 2 ≤ k ≤ n - 2}` (offset `4`). -/
def a (n : ℕ) : ℕ := (Finset.Icc 2 (n - 2)).gcd (Nat.choose n)

set_option maxRecDepth 100000 in
/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all `75` listed
terms `a(4), …, a(78)`. -/
theorem a_data : (List.range 75).map (fun i => a (i + 4)) =
    [6, 10, 5, 7, 14, 6, 3, 11, 11, 13, 13, 1, 2, 34, 17, 19, 19, 1, 1, 23, 23, 5, 5, 3, 3, 29,
     29, 31, 62, 2, 1, 1, 1, 37, 37, 1, 1, 41, 41, 43, 43, 1, 1, 47, 47, 7, 7, 1, 1, 53, 53, 1, 1,
     1, 1, 59, 59, 61, 61, 1, 2, 2, 1, 67, 67, 1, 1, 71, 71, 73, 73, 1, 1, 1, 1] := by
  decide +kernel

/-- A014963, the exponential of the von Mangoldt function: `1` unless `m` is a prime power
`p ^ k` (`p` prime, `k ≥ 1`), in which case it is that prime `p` (which is `m.minFac`). -/
def expMangoldt (m : ℕ) : ℕ := if IsPrimePow m then m.minFac else 1

/-- `expMangoldt m = exp (Λ m)`, with `Λ` Mathlib's von Mangoldt function. -/
theorem cast_expMangoldt (m : ℕ) :
    (expMangoldt m : ℝ) = Real.exp (ArithmeticFunction.vonMangoldt m) := by
  rw [ArithmeticFunction.vonMangoldt_apply, expMangoldt]
  split_ifs with h
  · rw [Real.exp_log]
    exact_mod_cast Nat.minFac_pos m
  · simp

set_option maxRecDepth 100000 in
/-- `expMangoldt` reproduces the `95` terms `A014963(1), …, A014963(95)` listed in OEIS
(kernel-checked). -/
theorem expMangoldt_data : (List.range 95).map (fun i => expMangoldt (i + 1)) =
    [1, 2, 3, 2, 5, 1, 7, 2, 3, 1, 11, 1, 13, 1, 1, 2, 17, 1, 19, 1, 1, 1, 23, 1, 5, 1, 3, 1, 29,
     1, 31, 2, 1, 1, 1, 1, 37, 1, 1, 1, 41, 1, 43, 1, 1, 1, 47, 1, 7, 1, 1, 1, 53, 1, 1, 1, 1, 1,
     59, 1, 61, 1, 1, 2, 1, 1, 67, 1, 1, 1, 71, 1, 73, 1, 1, 1, 1, 1, 79, 1, 3, 1, 83, 1, 1, 1, 1,
     1, 89, 1, 1, 1, 1, 1, 1] := by
  decide +kernel

/-- Jon Maiga's conjecture: for every `n ≥ 4`, `a(n) = A014963(n) * A014963(n - 1)`. -/
def statement : Prop :=
  ∀ n : ℕ, 4 ≤ n → a n = expMangoldt n * expMangoldt (n - 1)

/-- Robert Israel's conjecture (secondary, from the COMMENTS of the same entry): if `n ≥ 4` and
`a(n) > n`, then `n` is a Fermat prime `> 3` or `n - 1` is a Mersenne prime. -/
def statementIsrael : Prop :=
  ∀ n : ℕ, 4 ≤ n → n < a n →
    (n.Prime ∧ 3 < n ∧ ∃ k, n = Nat.fermatNumber k) ∨
      ((n - 1).Prime ∧ ∃ m, n - 1 = mersenne m)

end Math0.Statements.A328202
