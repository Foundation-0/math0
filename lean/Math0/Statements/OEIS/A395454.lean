/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A395454: a polynomial recurrence for the row polynomials of a binomial/Eulerian triangle

Source: https://oeis.org/A395454, Per W. Alexandersson, Jun 27 2026 (FORMULA section; the entry
itself is by Peter Luschny, Apr 23 2026). Verbatim:
> Conjecture: Let P(n) be the generating polynomial (in t) of row n. Then P(n) = (n - 2*t + n*t
> - 2)*P(n-1) + (t - t^2)*P'(n-1) + t*(2*n-4)*P(n-2).

The entry (offset `0`, keyword `tabl`) is "Triangle read by rows: T(n, k) = Sum_{j=0..n}
C(-j-1, -n-1)*E2(j, n-k), E2 the Eulerian numbers A201637", with Maple program
`A395454 := (n, k) -> add(binomial(-j-1, -n-1)*combinat:-eulerian2(j, n-k), j=0..n)`, and rows
`n = 0, 1, 2, …` with `0 ≤ k ≤ n`.

## Encoding

* *Second-order Eulerian numbers* (A201637, Concrete Mathematics / Maple indexing): `E2 n k`
  is given by `E2(0,0) = 1`, `E2(0,k) = 0` for `k ≥ 1`, and for `n ≥ 1` the recurrence of
  A201637, `E2(n,k) = (2n-1-k)·E2(n-1,k-1) + (k+1)·E2(n-1,k)` (with `E2(n-1,-1) = 0`, so
  `E2(n,0) = E2(n-1,0)`). It is computed in `ℤ`, so `2n-1-k` is honest integer subtraction.
* *The binomial factor.* Maple's `binomial(-j-1, -n-1)` (defined for negative integers by the
  Gamma-function limit) equals `(-1)^(n-j)·C(n,j)` for `0 ≤ j ≤ n`; that is what we use. So
  `T n k = ∑_{j=0}^{n} (-1)^(n-j)·C(n,j)·E2(j, n-k)` in `ℤ` (it is only used for `k ≤ n`, so
  `n - k` is the true difference).
* *Data.* `a` is the triangle read by rows (the OEIS sequence itself, offset `0`), and `a_data`
  checks all 55 listed terms (rows `0, …, 9`) as `a 0, …, a 54` in the kernel.
* *Row polynomials.* `P n = ∑_{k=0}^{n} T(n,k)·t^k ∈ ℤ[t]` is the generating polynomial of the
  row with index `n` in the entry's numbering (offset `0`: `P 0 = 1`, `P 1 = 0`, `P 2 = 2t`,
  `P 3 = 6t + 2t^2`, …). `P'` is the formal derivative in `t`.

## Reading of the conjecture

Read with the entry's row numbering (row `n` = `P n`, offset `0`), the recurrence is false at
every `n ≥ 2` for which it can be tested: already at `n = 2` the right-hand side is
`0·P(1) + (t - t^2)·P'(1) + t·0·P(0) = 0` (as `P 1 = 0`), while `P 2 = 2t`
(`not_statement_literal`, kernel-checked), and at `n = 3` it gives `4t` instead of
`6t + 2t^2`; an exact computation finds it false for every `n = 2, …, 19`. With the rows counted
from `1` instead (the `n`-th row is the row with index `n - 1`, i.e. `P(n)` of the conjecture is
`P (n - 1)` here) the same recurrence holds for all of `n = 3, …, 20` (exact computation, not
kernel-checked). So the conjecture is read as the claim it makes about the listed rows, with
the rows numbered from `1`, as the author's `P(n)` evidently does:

* `P1 n = P (n - 1)` is the generating polynomial of the `n`-th row counted from `1`
  (`P1 1 = 1`, `P1 2 = 0`, `P1 3 = 2t`, …; it is only used for `n ≥ 1`).
* `statement`: for every `n ≥ 3` (the range in which `P(n)`, `P(n-1)` and `P(n-2)` are all rows;
  the formula itself states no range, and at `n = 2` the would-be `P(0)` has the coefficient
  `2n - 4 = 0`), `P(n) = (n - 2t + n t - 2)·P(n-1) + (t - t^2)·P'(n-1) + t·(2n-4)·P(n-2)` in
  `ℤ[t]`, with `P = P1` and all coefficients `n - 2`, `2n - 4` read as integers. In the entry's
  numbering (`m = n - 1 ≥ 2`) this is
  `P_m = (m-1)(1+t)·P_{m-1} + (t - t^2)·P'_{m-1} + 2(m-1)t·P_{m-2}`.
* The literal reading with the entry's numbering is recorded as `statement_literal`, together
  with its refutation `not_statement_literal` at `n = 2`; it is not the primary formalization.
-/

namespace Math0.Statements.A395454

open Polynomial

/-- The second-order Eulerian numbers `E2(n, k)` of A201637 (Graham–Knuth–Patashnik indexing, as
in Maple's `combinat:-eulerian2`): `E2(0,0) = 1`, `E2(0,k) = 0` for `k ≥ 1`, and
`E2(n,k) = (2n-1-k)·E2(n-1,k-1) + (k+1)·E2(n-1,k)` for `n ≥ 1` (with `E2(n-1,-1) = 0`). -/
def E2 : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => E2 n 0
  | n + 1, k + 1 =>
      (2 * ((n : ℤ) + 1) - 1 - ((k : ℤ) + 1)) * E2 n k + ((k : ℤ) + 1 + 1) * E2 n (k + 1)

/-- `E2` reproduces rows `0, …, 8` of A201637 (kernel-checked). -/
theorem E2_data : (List.range 9).flatMap (fun n => (List.range (n + 1)).map (E2 n)) =
    [1, 1, 0, 1, 2, 0, 1, 8, 6, 0, 1, 22, 58, 24, 0, 1, 52, 328, 444, 120, 0, 1, 114, 1452,
      4400, 3708, 720, 0, 1, 240, 5610, 32120, 58140, 33984, 5040, 0, 1, 494, 19950, 195800,
      644020, 785304, 341136, 40320, 0] := by
  decide +kernel

/-- The triangle `T(n, k) = ∑_{j=0}^{n} binomial(-j-1, -n-1)·E2(j, n-k)` of A395454, where
Maple's `binomial(-j-1, -n-1) = (-1)^(n-j)·C(n, j)` for `0 ≤ j ≤ n`. Meaningful for `k ≤ n`. -/
def T (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (-1) ^ (n - j) * (n.choose j : ℤ) * E2 j (n - k)

/-- A395454 itself: the triangle `T` read by rows (`0 ≤ k ≤ n`), offset `0`. -/
def a (i : ℕ) : ℤ :=
  ((List.range (i + 1)).flatMap fun n => (List.range (n + 1)).map (T n)).getD i 0

/-- The definition reproduces all 55 terms listed in OEIS, `a 0, …, a 54` (rows `0, …, 9`;
kernel-checked). -/
theorem a_data : (List.range 55).map (fun i => a (i + 0)) =
    [1, 0, 0, 0, 2, 0, 0, 6, 2, 0, 0, 24, 34, 2, 0, 0, 120, 324, 98, 2, 0, 0, 720, 2988, 2096,
      234, 2, 0, 0, 5040, 28944, 34704, 9804, 514, 2, 0, 0, 40320, 300816, 533592, 276004,
      38856, 1082, 2, 0, 0, 362880, 3371040, 8137512, 6535272, 1766008, 139940, 2226, 2, 0] := by
  decide +kernel

/-- The generating polynomial (in `t`) of row `n` of the triangle:
`P(n) = ∑_{k=0}^{n} T(n,k)·t^k`. -/
noncomputable def P (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (T n k) * X ^ k

/-- The generating polynomial of the `n`-th row of the triangle counted from `1` (the row with
index `n - 1` in the entry's numbering): `P1 n = P (n - 1)`. Meaningful for `n ≥ 1`. -/
noncomputable def P1 (n : ℕ) : ℤ[X] := P (n - 1)

/-- Alexandersson's conjecture (A395454), with the rows counted from `1` (see the module
docstring): for all `n ≥ 3`,
`P(n) = (n - 2t + n t - 2)·P(n-1) + (t - t^2)·P'(n-1) + t·(2n-4)·P(n-2)`, where `P(n) = P1 n`. -/
def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    P1 n = ((n : ℤ[X]) - 2 * X + (n : ℤ[X]) * X - 2) * P1 (n - 1)
      + (X - X ^ 2) * derivative (P1 (n - 1))
      + X * (2 * (n : ℤ[X]) - 4) * P1 (n - 2)

/-- The literal reading of the conjecture with the entry's own row numbering (offset `0`,
`P(n) = P n`), for all `n ≥ 2`. Not the primary formalization: it fails at `n = 2`
(`not_statement_literal`). -/
def statement_literal : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    P n = ((n : ℤ[X]) - 2 * X + (n : ℤ[X]) * X - 2) * P (n - 1)
      + (X - X ^ 2) * derivative (P (n - 1))
      + X * (2 * (n : ℤ[X]) - 4) * P (n - 2)

theorem P_one : P 1 = 0 := by
  have h0 : T 1 0 = 0 := by decide +kernel
  have h1 : T 1 1 = 0 := by decide +kernel
  simp [P, Finset.sum_range_succ, h0, h1]

theorem P_two : P 2 = C 2 * X := by
  have h0 : T 2 0 = 0 := by decide +kernel
  have h1 : T 2 1 = 2 := by decide +kernel
  have h2 : T 2 2 = 0 := by decide +kernel
  simp [P, Finset.sum_range_succ, h0, h1, h2]

/-- The literal reading fails at `n = 2`: `P 2 = 2t`, but the right-hand side is `0`
(kernel-checked). -/
theorem not_statement_literal : ¬ statement_literal := by
  intro h
  have h2 := h 2 le_rfl
  have hc := congrArg (fun p : ℤ[X] => p.coeff 1) h2
  simp only [Nat.reduceSub, P_one, P_two, mul_zero, derivative_zero, zero_add] at hc
  norm_num at hc

end Math0.Statements.A395454
