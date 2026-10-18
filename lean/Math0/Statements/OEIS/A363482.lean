/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A363482: denominators of `1/(2-3/(3-4/(...(n-1)-n/(-5))))` are 1 or prime, except 49

Source: https://oeis.org/A363482, Mohammed Bouras, Jun 04 2023. Verbatim:
> Conjecture: Except for 49, every term of this sequence is either a prime or 1.

The sequence (offset 3) is the "Denominator of the continued fraction
1/(2-3/(3-4/(4-5/(...(n-1)-n/(-5)))))". The entry's examples fix the shape:
`a(3)` is the denominator of `1/(2 - 3/(-5)) = 5/13`, `a(4)` that of
`1/(2 - 3/(3 - 4/(-5))) = 19/23`, and `a(5)` that of `1/(2 - 3/(3 - 4/(4 - 5/(-5)))) = 11/7`.

## Encoding

The continued fraction is evaluated in `ℚ` from the inside out: start with `-5` and apply
`step k t = k - (k+1)/t` for `k = n-1, n-2, …, 2` (this is `List.foldr step (-5)` over
`[2, 3, …, n-1] = List.range' 2 (n - 2)`), then take the reciprocal. `a n` is the denominator
`Rat.den` of the resulting rational number in lowest terms (always positive, and `1` when the
value is an integer, e.g. `a 12 = 1`).

Lean's `x / 0 = 0` convention plays no role for `n ≥ 3`: no inner tail of the continued fraction
vanishes. (By the convergent recurrences, a vanishing tail would force the value to equal
`!m / 2` for some left factorial `!m`, while the value is `!(n-3)/2 + 5(n-1)(n-3)!/(2(n^2+3n-5))`;
this never happens for `n ≥ 3`. It was also checked by exact arithmetic for `3 ≤ n < 1200`.)
The definition reproduces all 61 terms listed in the entry (`a_data`, `n = 3, …, 63`). Values of
`a n` for `n < 3` are outside the sequence and are never used.

*Reading of "Except for 49".* The exception is the value `49` (which is `a 6`, see `a_data`):
every term `a n` with `n ≥ 3` that is not `49` is `1` or a prime.
-/

namespace Math0.Statements.A363482

/-- One level of the continued fraction: `step k t = k - (k+1)/t`. -/
def step (k : ℕ) (t : ℚ) : ℚ := (k : ℚ) - ((k : ℚ) + 1) / t

/-- The continued fraction `1/(2 - 3/(3 - 4/(4 - 5/(… (n-1) - n/(-5)))))`, evaluated from the
inside out: `step 2 (step 3 (… (step (n-1) (-5))))`, then the reciprocal. -/
def cf (n : ℕ) : ℚ := 1 / (List.range' 2 (n - 2)).foldr step (-5)

/-- A363482 (offset 3): the denominator of the continued fraction
`1/(2-3/(3-4/(4-5/(...(n-1)-n/(-5)))))`, in lowest terms. -/
def a (n : ℕ) : ℕ := (cf n).den

/-- The entry's examples: `a(3)`, `a(4)`, `a(5)` come from `5/13`, `19/23`, `11/7`. -/
example : cf 3 = 5 / 13 ∧ cf 4 = 19 / 23 ∧ cf 5 = 11 / 7 := by decide +kernel

/-- The definition reproduces all 61 terms listed in OEIS, `a 3, …, a 63` (kernel-checked). -/
theorem a_data : (List.range 61).map (fun i => a (i + 3)) =
    [13, 23, 7, 49, 13, 83, 103, 5, 149, 1, 29, 233, 53, 23, 67, 373, 59, 1, 499, 109, 593, 643,
      139, 107, 1, 863, 71, 197, 1049, 223, 1, 179, 53, 1399, 59, 1553, 71, 1, 257, 1, 1973, 2063,
      431, 173, 67, 349, 2543, 1, 2749, 571, 2963, 439, 1, 3299, 683, 3533, 281, 151, 557, 1,
      4153] := by
  decide +kernel

/-- Conjecture (Mohammed Bouras, 2023): except for `49`, every term `a n` (`n ≥ 3`) of the
sequence is either a prime or `1`. -/
def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → a n ≠ 49 → a n = 1 ∨ (a n).Prime

end Math0.Statements.A363482
