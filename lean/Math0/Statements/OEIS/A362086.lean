/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A362086: denominators of `1/(2-3/(3-4/(...(n-1)-n/(-3))))` are 1 or prime, except 9

Source: https://oeis.org/A362086, Mohammed Bouras, May 28 2023. Verbatim:
> Conjecture: Except for 9, every term of this sequence is either a prime or 1.

The sequence (offset 3) is the "Denominator of the continued fraction
1/(2-3/(3-4/(4-5/(...(n-1)-n/(-3)))))". The entry's examples fix the shape:
`a(3)` is the denominator of `1/(2 - 3/(-3)) = 1/3`, `a(4)` that of
`1/(2 - 3/(3 - 4/(-3))) = 13/17`, and `a(5)` that of `1/(2 - 3/(3 - 4/(4 - 5/(-3)))) = 13/9`.

## Encoding

The continued fraction is evaluated in `ℚ` from the inside out: start with `-3` and apply
`step k t = k - (k+1)/t` for `k = n-1, n-2, …, 2` (this is `List.foldr step (-3)` over
`[2, 3, …, n-1] = List.range' 2 (n - 2)`), then take the reciprocal. `a n` is the denominator
`Rat.den` of the resulting rational number in lowest terms (always positive, and `1` when the
value is an integer, e.g. `a 21 = 1`).

Lean's `x / 0 = 0` convention plays no role for `n ≥ 3`: no inner tail of the continued fraction
vanishes. (The innermost value `-3` is nonzero; the tail `t_{n-1} = (n-1) + n/3` is `≥ 2`, the
tails `t_k` with `5 ≤ k < n-1` are then `≥ (k-1)/2 ≥ 2`, `t_4 ≥ 3/2` and `t_3 ≥ 1/3`, so all tails
`t_k`, `k ≥ 3`, are positive. The numbers `u_k = k(k-2)/(k-1)` satisfy `u_k = k - (k+1)/u_{k+1}`
and `u_2 = 0`, so by injectivity of `t ↦ k - (k+1)/t` a vanishing outer tail `t_2 = 0` would
force `t_{n-1} = (n-1)(n-3)/(n-2) < n-1`, which is false. It was also checked by exact arithmetic
for `3 ≤ n < 1500`.) The definition reproduces all 57 terms listed in the entry (`a_data`,
`n = 3, …, 59`). Values of `a n` for `n < 3` are outside the sequence and are never used.

*Reading of "Except for 9".* The exception is the value `9` (which is `a 5`, see `a_data`):
every term `a n` with `n ≥ 3` that is not `9` is `1` or a prime.
-/

namespace Math0.Statements.A362086

/-- One level of the continued fraction: `step k t = k - (k+1)/t`. -/
def step (k : ℕ) (t : ℚ) : ℚ := (k : ℚ) - ((k : ℚ) + 1) / t

/-- The continued fraction `1/(2 - 3/(3 - 4/(4 - 5/(… (n-1) - n/(-3)))))`, evaluated from the
inside out: `step 2 (step 3 (… (step (n-1) (-3))))`, then the reciprocal. -/
def cf (n : ℕ) : ℚ := 1 / (List.range' 2 (n - 2)).foldr step (-3)

/-- A362086 (offset 3): the denominator of the continued fraction
`1/(2-3/(3-4/(4-5/(...(n-1)-n/(-3)))))`, in lowest terms. -/
def a (n : ℕ) : ℕ := (cf n).den

/-- The entry's examples: `a(3)`, `a(4)`, `a(5)` come from `1/3`, `13/17`, `13/9`. -/
example : cf 3 = 1 / 3 ∧ cf 4 = 13 / 17 ∧ cf 5 = 13 / 9 := by decide +kernel

/-- The definition reproduces all 57 terms listed in OEIS, `a 3, …, a 59` (kernel-checked). -/
theorem a_data : (List.range 57).map (fun i => a (i + 3)) =
    [3, 17, 9, 13, 53, 23, 29, 107, 43, 17, 179, 23, 79, 269, 101, 113, 29, 139, 1, 503, 61,
      199, 647, 233, 251, 809, 17, 103, 43, 1, 373, 1187, 419, 443, 61, 1, 173, 1637, 191,
      601, 1889, 659, 53, 127, 751, 1, 2447, 283, 883, 2753, 953, 1, 181, 1063, 367, 263,
      131] := by
  decide +kernel

/-- Conjecture (Mohammed Bouras, 2023): except for `9`, every term `a n` (`n ≥ 3`) of the
sequence is either a prime or `1`. -/
def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → a n ≠ 9 → a n = 1 ∨ (a n).Prime

end Math0.Statements.A362086
