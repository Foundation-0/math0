/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A356360: denominators of `1/(2-3/(3-4/(...(n-1)-n/(n+1))))` are 1 or prime

Source: https://oeis.org/A356360, Mohammed Bouras, Oct 15 2022. Verbatim:
> Conjecture: The sequence contains only 1's and the primes.

The sequence (offset 3) is the "Denominator of the continued fraction
1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+1)))))". For `n = 3` the innermost level `(n-1) - n/(n+1)`
is already the outer one, giving `1/(2 - 3/4) = 4/5`, so `a(3) = 5`; next
`1/(2 - 3/(3 - 4/5)) = 11/7` and `1/(2 - 3/(3 - 4/(4 - 5/6))) = 11/3`, giving `a(4) = 7`,
`a(5) = 3`, as listed.

## Encoding

The continued fraction is evaluated in `ℚ` from the inside out: start with `n + 1` and apply
`step k t = k - (k+1)/t` for `k = n-1, n-2, …, 2` (this is `List.foldr step (n + 1)` over
`[2, 3, …, n-1] = List.range' 2 (n - 2)`), then take the reciprocal. `a n` is the denominator
`Rat.den` of the resulting rational number in lowest terms (always positive, and `1` when the
value is an integer, e.g. `a 8 = 1`).

Lean's `x / 0 = 0` convention plays no role for `n ≥ 3`: no tail of the continued fraction
vanishes. (The numbers `u_k = k(k-2)/(k-1)` satisfy `u_k = k - (k+1)/u_{k+1}`, `u_2 = 0` and
`u_k > 0` for `k ≥ 3`. The innermost value `n + 1` exceeds `u_n`, and `t ↦ k - (k+1)/t` is
increasing for `t > 0`, so by downward induction every tail `t_k` (`2 ≤ k ≤ n-1`) satisfies
`t_k > u_k ≥ 0`. It was also checked by exact arithmetic for `3 ≤ n < 800`.)
The definition reproduces all 82 terms listed in the entry (`a_data`, `n = 3, …, 84`). Values of
`a n` for `n < 3` are outside the sequence and are never used.

*Reading of the conjecture.* "The sequence contains only 1's and the primes" is read as: every
term `a n` with `n ≥ 3` (the offset) is `1` or a prime. (It does not claim that every prime
occurs.)
-/

namespace Math0.Statements.A356360

/-- One level of the continued fraction: `step k t = k - (k+1)/t`. -/
def step (k : ℕ) (t : ℚ) : ℚ := (k : ℚ) - ((k : ℚ) + 1) / t

/-- The continued fraction `1/(2 - 3/(3 - 4/(4 - 5/(… (n-1) - n/(n+1)))))`, evaluated from the
inside out: `step 2 (step 3 (… (step (n-1) (n+1))))`, then the reciprocal. -/
def cf (n : ℕ) : ℚ := 1 / (List.range' 2 (n - 2)).foldr step ((n : ℚ) + 1)

/-- A356360 (offset 3): the denominator of the continued fraction
`1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+1)))))`, in lowest terms. -/
def a (n : ℕ) : ℕ := (cf n).den

/-- The first values: `cf 3 = 1/(2 - 3/4) = 4/5`, `cf 4 = 11/7`, `cf 5 = 11/3`. -/
example : cf 3 = 4 / 5 ∧ cf 4 = 11 / 7 ∧ cf 5 = 11 / 3 := by decide +kernel

/-- The definition reproduces all 82 terms listed in OEIS, `a 3, …, a 84` (kernel-checked). -/
theorem a_data : (List.range 82).map (fun i => a (i + 3)) =
    [5, 7, 3, 11, 13, 1, 17, 19, 1, 23, 1, 1, 29, 31, 1, 1, 37, 1, 41, 43, 1, 47, 1, 1, 53, 1,
      1, 59, 61, 1, 1, 67, 1, 71, 73, 1, 1, 79, 1, 83, 1, 1, 89, 1, 1, 1, 97, 1, 101, 103, 1,
      107, 109, 1, 113, 1, 1, 1, 1, 1, 1, 127, 1, 131, 1, 1, 137, 139, 1, 1, 1, 1, 149, 151, 1,
      1, 157, 1, 1, 163, 1, 167] := by
  decide +kernel

/-- Conjecture (Mohammed Bouras, 2022): the sequence contains only 1's and the primes, i.e.
every term `a n` (`n ≥ 3`) is either `1` or a prime. -/
def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ (a n).Prime

end Math0.Statements.A356360
