/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A393794: fixed points of the 1089-trick map

Source: https://oeis.org/A393794, _Remco Havenaar_, Feb 27 2026. Verbatim (COMMENTS section):
> a(n) is the unique fixed point of the 1089-trick map T among all (n+4)-digit numbers (verified
> exhaustively for n = 1..4; conjectured for all n >= 1).

The entry's name: "Fixed points of the 1089-trick map
T(n) = |n - reverse(n)| + reverse(|n - reverse(n)|)."

## Encoding

* `rev m` is `reverse(m)` (A004086): the decimal digits of `m` read backwards, as a number, so
  leading zeros drop (`rev 10890 = 9801`, as in the entry's example `10890 - 09801 = 1089`).
  It is `Nat.ofDigits 10 (Nat.digits 10 m).reverse` (`Nat.digits` is little-endian).
* `T x = D + rev D` with `D = |x - rev x|`, the absolute difference taken as `Nat.dist`
  (no truncated subtraction).
* `a n = 110 * (10 ^ (n + 1) - 1)` for `n ≥ 1` (offset 1). This is the entry's formula
  `a(n) = 110*(10^(n+1) - 1)`, which its data, Mathematica and Python programs all use to
  generate the terms, and which its comment proves to be a fixed point of `T`. The conjecture
  (the comment quoted above) is exactly the claim that these terms are the only fixed points
  of their digit lengths, so `a` is not defined as "the `n`-th fixed point of `T`": that
  reading of the name would make the conjecture assume what it claims. (`a 0 = 990` lies outside
  the offset and is not used.) Kernel checks below: `a` reproduces all 18 listed terms
  (`a_data`); `T` fixes each of them and each `a (i + 1)` has `i + 5` digits (`T_data`,
  `digits_data`); and `10890 = a 1` is the least positive fixed point of `T`
  (`least_fixed_point`), matching the name.
* "(n+4)-digit numbers" are the `x` with `(Nat.digits 10 x).length = n + 4`, i.e.
  `10 ^ (n + 3) ≤ x < 10 ^ (n + 4)`.
* The statement covers every `n ≥ 1`, as the comment says ("conjectured for all n >= 1"; the
  exhaustive checks for `n = 1..4` are part of that range). "a(n) is the unique fixed point
  among all (n+4)-digit numbers" is encoded in full: `a n` has `n + 4` digits, `T (a n) = a n`,
  and every `(n + 4)`-digit `x` with `T x = x` equals `a n`.
-/

namespace Math0.Statements.A393794

/-- `reverse(m)` (A004086): the number whose decimal digits are those of `m` in reverse order
(leading zeros of the result are dropped). -/
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse

/-- The 1089-trick map `T(x) = |x - reverse(x)| + reverse(|x - reverse(x)|)`. -/
def T (x : ℕ) : ℕ := Nat.dist x (rev x) + rev (Nat.dist x (rev x))

/-- A393794: `a(n) = 110 * (10^(n+1) - 1)` (`n ≥ 1`), the fixed points `10890, 109890,
1099890, …` of the 1089-trick map `T` listed in the entry; `a(n)` has `n + 4` digits. -/
def a (n : ℕ) : ℕ := 110 * (10 ^ (n + 1) - 1)

/-- The definition reproduces all 18 terms listed in OEIS (offset 1, kernel-checked). -/
theorem a_data : (List.range 18).map (fun i => a (i + 1)) =
    [10890, 109890, 1099890, 10999890, 109999890, 1099999890, 10999999890, 109999999890,
      1099999999890, 10999999999890, 109999999999890, 1099999999999890, 10999999999999890,
      109999999999999890, 1099999999999999890, 10999999999999999890, 109999999999999999890,
      1099999999999999999890] := by
  decide +kernel

/-- `T` fixes each of the 18 listed terms (kernel-checked). -/
theorem T_data : (List.range 18).all (fun i => T (a (i + 1)) == a (i + 1)) = true := by
  decide +kernel

/-- Each of the 18 listed terms `a (i + 1)` has `i + 5` decimal digits (kernel-checked). -/
theorem digits_data :
    (List.range 18).all (fun i => (Nat.digits 10 (a (i + 1))).length == i + 5) = true := by
  decide +kernel

/-- `10890 = a 1` is the least positive fixed point of `T` (kernel-checked; `T 0 = 0`). -/
theorem least_fixed_point :
    T (a 1) = a 1 ∧ (List.range (a 1)).all (fun x => x == 0 || T x != x) = true := by
  decide +kernel

/-- Conjecture (Havenaar, A393794): for every `n ≥ 1`, `a(n)` is the unique fixed point of the
1089-trick map `T` among all `(n + 4)`-digit numbers. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (Nat.digits 10 (a n)).length = n + 4 ∧ T (a n) = a n ∧
      ∀ x : ℕ, (Nat.digits 10 x).length = n + 4 → T x = x → x = a n

end Math0.Statements.A393794
