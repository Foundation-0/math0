/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A175385: `∑_{i=1..n} C(2n-i-1, i-1)/i` is never an integer for `n > 1`

Source: https://oeis.org/A175385, _Vladimir Shevelev_, _Zak Seidov_, Apr 24 2010. Verbatim
(COMMENTS section):
> We conjecture that Sum_{i=1..n} ((1/i)*C(2n-i-1,i-1)) is not an integer for n>1.

The sequence (offset `1`) is "a(n) = numerator of Sum_{i=1..n} binomial(2n-i-1,i-1)/i."
(the denominators are A175386).

## Encoding

* `S n : ℚ` is the sum `∑_{i=1}^{n} C(2n-i-1, i-1)/i`, computed exactly in `ℚ` with Mathlib's
  `Nat.choose`. For `1 ≤ i ≤ n` the natural-number subtractions `2n-i-1` and `i-1` are never
  truncated (`2n-i-1 ≥ n-1 ≥ 0`), so this is literally the entry's sum. For `n = 0` the sum is
  empty; that value is outside the sequence and never used.
* `a n` is the numerator of `S n` in lowest terms (`Rat.num`, as a natural number via
  `Int.natAbs`; `S n > 0` for `n ≥ 1`). It uses the OEIS offset `1` and reproduces all 27
  listed terms (`a_data`).
* "Is not an integer" is read as: there is no integer `k` with `S n = k` in `ℚ`. The range
  "for n>1" is `n ≥ 2` over the natural numbers.
-/

namespace Math0.Statements.A175385

/-- The sum `∑_{i=1}^{n} C(2n-i-1, i-1)/i`, computed exactly in `ℚ`. -/
def S (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 n, ((Nat.choose (2 * n - i - 1) (i - 1) : ℕ) : ℚ) / (i : ℚ)

/-- A175385 (offset `1`): the numerator, in lowest terms, of
`∑_{i=1..n} binomial(2n-i-1, i-1)/i`. -/
def a (n : ℕ) : ℕ := (S n).num.natAbs

/-- The definition reproduces all 27 terms listed in OEIS, `a 1, …, a 27` (kernel-checked). -/
theorem a_data : (List.range 27).map (fun i => a (i + 1)) =
    [1, 3, 17, 23, 61, 107, 421, 1103, 5777, 7563, 19801, 103681, 135721, 355323, 1860497,
      2435423, 6376021, 11128427, 43701901, 114413063, 599074577, 784198803, 2053059121,
      10749957121, 14071876561, 36840651123, 192900153617] := by
  decide +kernel

/-- Conjecture (Shevelev and Seidov, A175385): for every `n > 1`, the sum
`∑_{i=1..n} C(2n-i-1, i-1)/i` is not an integer. -/
def statement : Prop :=
  ∀ n : ℕ, 1 < n → ¬ ∃ k : ℤ, S n = (k : ℚ)

end Math0.Statements.A175385
