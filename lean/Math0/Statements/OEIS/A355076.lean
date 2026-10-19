/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A355076: denominators of the partial sums of `fusc(k)/fusc(k+1)`

Source: https://oeis.org/A355076, _Rémy Sigrist_, Jun 18 2022 (FORMULA section). Verbatim:
> Conjecture: a(n) = 1 for n of the form 2*4^k - 1 or 2*4^k - 2 for some k >= 0.

The entry's definition (offset `0`): "a(n) is the denominator of Sum_{k = 0..n} fusc(k)/fusc(k+1)
(where fusc is Stern's diatomic series A002487)." A002487 (offset `0`) is "a(0) = 0, a(1) = 1;
for n > 0: a(2*n) = a(n), a(2*n+1) = a(n) + a(n+1)."

## Encoding

* `fusc` is computed by the defining recursion of A002487 with a fuel argument (`fuscAux`), so
  that the kernel can evaluate it. With fuel `n + 1` the recursion is never cut off: every
  recursive call is on a strictly smaller argument (`n / 2 < n` and `n / 2 + 1 < n` for
  `n ≥ 2`). The theorems `fusc_zero`, `fusc_one`, `fusc_even`, `fusc_odd` prove that `fusc`
  satisfies exactly the defining equations of A002487 (the last two for every `n`, which
  includes the entry's range `n > 0`), and these equations determine the sequence.
  `fusc_data` checks the 92 terms of A002487 listed in OEIS.
* `a n` is the denominator (`Rat.den`, the denominator of the reduced fraction, always `≥ 1`) of
  the rational number `∑_{k=0}^{n} fusc(k)/fusc(k+1)`, computed exactly in `ℚ`. The divisors
  `fusc(k+1)` are all nonzero (`fusc m > 0` for `m ≥ 1`), so Lean's convention `x / 0 = 0` plays
  no role. `a_data` checks all 53 listed terms `a 0, …, a 52`.
* The conjecture is stated literally: for every `n` such that `n = 2*4^k - 1` or
  `n = 2*4^k - 2` for some `k ≥ 0`, `a n = 1`. Since `2*4^k ≥ 2`, the natural-number
  subtractions are exact (`k = 0` gives `n = 1` and `n = 0`).
-/

namespace Math0.Statements.A355076

/-- The defining recursion of A002487 run with `fuel` steps (it returns `0` when the fuel is
exhausted, which never happens for `fuel > n`; see `fuscAux_eq_fuscAux`). -/
def fuscAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
    if n ≤ 1 then n
    else if n % 2 = 0 then fuscAux fuel (n / 2)
    else fuscAux fuel (n / 2) + fuscAux fuel (n / 2 + 1)

/-- Stern's diatomic series A002487: `fusc 0 = 0`, `fusc 1 = 1`, `fusc (2n) = fusc n`,
`fusc (2n+1) = fusc n + fusc (n+1)`. -/
def fusc (n : ℕ) : ℕ := fuscAux (n + 1) n

/-- The fueled recursion does not depend on the fuel once the fuel exceeds the argument. -/
theorem fuscAux_eq_fuscAux : ∀ (f g n : ℕ), n < f → n < g → fuscAux f n = fuscAux g n := by
  intro f
  induction f with
  | zero => intro g n hf; omega
  | succ f ih =>
    intro g n hf hg
    cases g with
    | zero => omega
    | succ g =>
      simp only [fuscAux]
      split_ifs with h1 h2
      · rfl
      · exact ih g (n / 2) (by omega) (by omega)
      · rw [ih g (n / 2) (by omega) (by omega), ih g (n / 2 + 1) (by omega) (by omega)]

theorem fuscAux_succ (fuel n : ℕ) : fuscAux (fuel + 1) n =
    if n ≤ 1 then n
    else if n % 2 = 0 then fuscAux fuel (n / 2)
    else fuscAux fuel (n / 2) + fuscAux fuel (n / 2 + 1) := rfl

theorem fuscAux_eq_fusc (f n : ℕ) (h : n < f) : fuscAux f n = fusc n :=
  fuscAux_eq_fuscAux f (n + 1) n h (by omega)

theorem fusc_zero : fusc 0 = 0 := by decide +kernel

theorem fusc_one : fusc 1 = 1 := by decide +kernel

/-- `fusc (2n) = fusc n` for all `n`. -/
theorem fusc_even (n : ℕ) : fusc (2 * n) = fusc n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · show fuscAux (2 * n + 1) (2 * n) = fusc n
    rw [fuscAux_succ]
    rw [if_neg (by omega), if_pos (by omega), show 2 * n / 2 = n by omega]
    exact fuscAux_eq_fusc _ _ (by omega)

/-- `fusc (2n+1) = fusc n + fusc (n+1)` for all `n`. -/
theorem fusc_odd (n : ℕ) : fusc (2 * n + 1) = fusc n + fusc (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · show fuscAux (2 * n + 1 + 1) (2 * n + 1) = fusc n + fusc (n + 1)
    rw [fuscAux_succ]
    rw [if_neg (by omega), if_neg (by omega), show (2 * n + 1) / 2 = n by omega]
    rw [fuscAux_eq_fusc _ _ (by omega), fuscAux_eq_fusc _ _ (by omega)]

/-- `fusc` reproduces the 92 terms of A002487 listed in OEIS (kernel-checked). -/
theorem fusc_data : (List.range 92).map fusc =
    [0, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3, 5, 2, 5, 3, 4, 1, 5, 4, 7, 3, 8, 5, 7, 2, 7, 5, 8, 3, 7,
     4, 5, 1, 6, 5, 9, 4, 11, 7, 10, 3, 11, 8, 13, 5, 12, 7, 9, 2, 9, 7, 12, 5, 13, 8, 11, 3,
     10, 7, 11, 4, 9, 5, 6, 1, 7, 6, 11, 5, 14, 9, 13, 4, 15, 11, 18, 7, 17, 10, 13, 3, 14, 11,
     19, 8, 21, 13, 18, 5, 17, 12, 19] := by
  decide +kernel

/-- A355076: `a(n)` is the denominator of `∑_{k=0}^{n} fusc(k)/fusc(k+1)` (a rational number,
in lowest terms), where `fusc` is Stern's diatomic series A002487. -/
def a (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.range (n + 1), ((fusc k : ℚ) / (fusc (k + 1) : ℚ))).den

/-- The definition reproduces all 53 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 53).map a =
    [1, 1, 2, 2, 6, 3, 1, 1, 4, 12, 60, 60, 12, 4, 2, 2, 10, 20, 140, 420, 840, 840, 840, 840,
     840, 840, 420, 140, 20, 5, 1, 1, 6, 30, 90, 180, 1980, 13860, 13860, 13860, 13860, 27720,
     360360, 72072, 72072, 72072, 8008, 8008, 72072, 72072, 72072, 360360, 27720] := by
  decide +kernel

/-- Conjecture (Rémy Sigrist, 2022): `a(n) = 1` (i.e. `∑_{k=0}^{n} fusc(k)/fusc(k+1)` is an
integer) for every `n` of the form `2*4^k - 1` or `2*4^k - 2` with `k ≥ 0`. -/
def statement : Prop :=
  ∀ n : ℕ, (∃ k : ℕ, n = 2 * 4 ^ k - 1 ∨ n = 2 * 4 ^ k - 2) → a n = 1

end Math0.Statements.A355076
