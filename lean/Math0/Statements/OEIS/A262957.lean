/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A262957: Israel's recurrence for `1 - 1/(2 + 1/(3 - 1/(4 + …)))` gives coprime pairs

Source: https://oeis.org/A262957, _Robert Israel_, Dec 22 2015 (comment in the entry by
_Mohamed Sabba_). Verbatim (COMMENTS section):
> From _Robert Israel_, Dec 22 2015: (Start)
> a(n) is the numerator of b(n)/c(n) where
> b(1) = 2, b(2) = 3, c(1) = 3, c(2) = 5,
> b(n+1) = (((-1)^n*(n-1)+n*(n+2))*b(n) - (1+(-1)^n*(n+1))*b(n-1))/(n-(-1)^n),
> c(n+1) = (((-1)^n*(n-1)+n*(n+2))*c(n) - (1+(-1)^n*(n+1))*c(n-1))/(n-(-1)^n).
> Conjecture: b(n) and c(n) are coprime for all n, so that a(n) = b(n).
> I have verified this for n <= 10000. (End)

The sequence (offset `1`) is "Numerators of the n-th iteration of the alternating continued
fraction formed from the positive integers, starting with (1 - ...)". The examples fix the
meaning of "n-th iteration": `a(1)`: `1-1/(2+1) = 2/3`, `a(2)`: `1-1/(2+1/(3-1)) = 3/5`,
`a(3)`: `1-1/(2+1/(3-1/(4+1))) = 19/33`, i.e. the integers `1, 2, …, n+1` are used, the sign
after `k` is `(-1)^k`, and the innermost tail is `1` (this is also what the entry's PARI
program computes).

## Encoding

* `cf n : ℚ` is the `n`-th iteration `1 - 1/(2 + 1/(3 - … (n+1) + (-1)^(n+1)/1))`, computed
  exactly in `ℚ` as the right fold of `k, t ↦ k + (-1)^k / t` over `[1, 2, …, n+1]` starting
  from `t = 1`. For `n ≥ 1` no intermediate denominator vanishes (each inner value is `≥ 1`),
  so Lean's convention `x / 0 = 0` never intervenes.
* `a n` is the numerator of `cf n` in lowest terms (`Rat.num`, as a natural number via
  `Int.natAbs`, matching the PARI program's `denominator(1/t)`; `cf n > 0` for `n ≥ 1`). It uses
  the OEIS offset `1` and reproduces all 22 listed terms (`a_data`).
* `b n`, `c n : ℚ` are Israel's sequences, defined literally by the displayed recurrence in `ℚ`
  (the recurrence involves a division, so they are a priori rationals). `b 0`, `c 0` are
  never used (the recurrence starts at index 1); the step for `b (n+1)` is applied for `n ≥ 2`,
  where the divisor `n - (-1)^n` is nonzero.
* The conjecture is read as: for every `n ≥ 1` (the indexing of `b`, `c` starts at `1`),
  `b n` and `c n` are integers `p`, `q` with `gcd(p, q) = 1`, and the stated consequence
  `a(n) = b(n)` holds. Both parts of the sentence "b(n) and c(n) are coprime for all n, so that
  a(n) = b(n)" are included in `statement`; the second part also relies on Israel's (unproved
  in the entry) assertion that `a(n)` is the numerator of `b(n)/c(n)`.
-/

namespace Math0.Statements.A262957

/-- The `n`-th iteration of the alternating continued fraction
`1 - 1/(2 + 1/(3 - 1/(4 + … (n+1) ± 1/1)))`: the right fold of `k, t ↦ k + (-1)^k / t` over
`k = 1, 2, …, n+1`, starting from the innermost value `1`. -/
def cf (n : ℕ) : ℚ :=
  (List.range' 1 (n + 1)).foldr (fun (k : ℕ) (t : ℚ) => (k : ℚ) + (-1) ^ k / t) 1

/-- A262957 (offset `1`): the numerator, in lowest terms, of the `n`-th iteration of the
alternating continued fraction `1 - 1/(2 + 1/(3 - 1/(4 + …)))`. -/
def a (n : ℕ) : ℕ := (cf n).num.natAbs

/-- The definition reproduces all 22 terms listed in OEIS, `a 1, …, a 22` (kernel-checked). -/
theorem a_data : (List.range 22).map (fun i => a (i + 1)) =
    [2, 3, 19, 64, 538, 2833, 29169, 210308, 2572158, 23595915, 334778571, 3732092084,
      60305234822, 791741083537, 14359827157009, 217037153818264, 4366918714540522,
      74685204276602819, 1651116684587556019, 31524723785455714840, 759659139498065625218,
      16017463672140861567617] := by
  decide +kernel

/-- One step of Israel's recurrence at index `m`: given `x(m-1) = u` and `x(m) = v`, returns
`x(m+1) = (((-1)^m*(m-1) + m*(m+2))*x(m) - (1 + (-1)^m*(m+1))*x(m-1)) / (m - (-1)^m)`. -/
def step (m : ℕ) (u v : ℚ) : ℚ :=
  (((-1) ^ m * ((m : ℚ) - 1) + (m : ℚ) * ((m : ℚ) + 2)) * v
      - (1 + (-1) ^ m * ((m : ℚ) + 1)) * u) / ((m : ℚ) - (-1) ^ m)

/-- The pair `(x(n+1), x(n+2))` of the sequence with `x(1) = x₁`, `x(2) = x₂` and
`x(m+1) = step m (x(m-1)) (x(m))` for `m ≥ 2`. -/
def israelPair (x₁ x₂ : ℚ) : ℕ → ℚ × ℚ
  | 0 => (x₁, x₂)
  | n + 1 =>
    let p := israelPair x₁ x₂ n
    (p.2, step (n + 2) p.1 p.2)

/-- Israel's `b(n)` (`n ≥ 1`): `b(1) = 2`, `b(2) = 3`,
`b(n+1) = (((-1)^n*(n-1)+n*(n+2))*b(n) - (1+(-1)^n*(n+1))*b(n-1))/(n-(-1)^n)`.
(`b 0` is an unused junk value.) -/
def b (n : ℕ) : ℚ := (israelPair 2 3 (n - 1)).1

/-- Israel's `c(n)` (`n ≥ 1`): `c(1) = 3`, `c(2) = 5`, same recurrence as `b`.
(`c 0` is an unused junk value.) -/
def c (n : ℕ) : ℚ := (israelPair 3 5 (n - 1)).1

/-- Sanity check: `b` and `c` satisfy the stated initial values and the recurrence at
`n = 2, 3`, and give `b(3)/c(3) = 19/33`, `b(4)/c(4) = 64/111` (as in the OEIS examples). -/
theorem bc_data : (List.range 6).map (fun i => (b (i + 1), c (i + 1))) =
    [(2, 3), (3, 5), (19, 33), (64, 111), (538, 933), (2833, 4913)] := by
  decide +kernel

/-- Conjecture (Robert Israel, A262957): for all `n ≥ 1`, `b(n)` and `c(n)` are coprime
integers, so that `a(n) = b(n)`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ p q : ℤ, b n = (p : ℚ) ∧ c n = (q : ℚ) ∧ Int.gcd p q = 1 ∧
      ((a n : ℕ) : ℚ) = b n

end Math0.Statements.A262957
