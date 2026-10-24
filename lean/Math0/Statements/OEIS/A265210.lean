/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A265210: columns of the reversed ternary digits of `2^n`

Source: https://oeis.org/A265210, L. Edson Jeffery, Dec 04 2015 (COMMENTS section). Verbatim:
> Conjecture 1: The sequence in column k is periodic, with period p(k) = 2*3^(k-1) =
> A008776(k-1), k >= 1, and in which the numbers 0,1,2 appear with equal frequency, for each
> k>1.

The entry (L. Edson Jeffery, Dec 04 2015, offset `0`) is "Irregular triangle read by rows in
which row n lists the base 3 digits of 2^n in reverse order, n >= 0." Data:
`1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 0, …` (84 terms, rows `n = 0, …, 15`).

## Encoding

* *The triangle.* `row n = Nat.digits 3 (2 ^ n)` is row `n` (`n ≥ 0`): `Nat.digits` lists the
  base-3 digits least significant first, i.e. the base-3 digits of `2^n` "in reverse order"
  (row `5`: `2^5 = 1012₃`, `row 5 = [2, 1, 0, 1]`, as in the entry's example). Every row is
  nonempty (`2^n > 0`).
* *The sequence.* `a m` is the `m`-th term (offset `0`) of the triangle read by rows, i.e. the
  `m`-th entry of the concatenation `row 0 ++ row 1 ++ ⋯`. Since every row is nonempty, the
  first `m + 1` rows already contain at least `m + 1` entries, so
  `a m = (row 0 ++ ⋯ ++ row m)[m]` (the default `0` of `getD` is never used).
  `a_data` checks all 84 listed terms.
* *Columns.* Column `k` (`k ≥ 1`) consists of the `k`-th entries of the rows, read top to bottom.
  `T n k = (row n)[k-1]` is the entry of row `n` in column `k`; it exists iff
  `k ≤ (row n).length`, i.e. iff `3^(k-1) ≤ 2^n`. Since the row lengths are nondecreasing in
  `n`, column `k` is the sequence `T n₀ k, T (n₀+1) k, …`, where `n₀` is the first row of
  length `≥ k`; the rows with an entry in column `k` are exactly the `n ≥ n₀`. (Column `1` is
  `1, 2, 1, 2, …`; column `2` starts at row `2`: `1, 2, 2, 1, 0, 0, 1, …`; see `col1_data`,
  `col2_data`, `col3_data`.)
* *Periods.* `IsColPeriod k q` says that `q` is a period of column `k`: `T (n + q) k = T n k`
  for every row `n` that has an entry in column `k` (then so does row `n + q`). As a statement
  about the column read as a sequence `c(j) = T (n₀ + j) k`, `j ≥ 0`, this is exactly
  `∀ j, c (j + q) = c j`.
* *Reading choices.*
  - "periodic, with period p(k)" is read as: `p(k) = 2*3^(k-1)` is *the* (least positive)
    period of column `k`, i.e. `p(k)` is a period and no `q` with `0 < q < p(k)` is a period
    (every positive multiple of a period would also be a period, so naming the specific value
    `p(k)` refers to the least one). This part is asserted for every `k ≥ 1`.
  - "the numbers 0,1,2 appear with equal frequency, for each k>1" is read as: for every
    `k ≥ 2`, in every block of `p(k)` consecutive terms of column `k` (rows `m, …, m+p(k)-1`
    with `m ≥ n₀`), the digits `0`, `1` and `2` occur the same number of times. Given the
    periodicity part (a conjunct of the same statement), this is equivalent to each of
    `0, 1, 2` having the same asymptotic frequency (necessarily `1/3`) in column `k`, and also
    to equal counts in a single period; so the whole statement does not depend on this choice.
-/

namespace Math0.Statements.A265210

/-- Row `n` of the triangle: the base-3 digits of `2^n` in reverse order (least significant
digit first). -/
def row (n : ℕ) : List ℕ := Nat.digits 3 (2 ^ n)

/-- A265210: the triangle whose row `n` lists the base-3 digits of `2^n` in reverse order, read
by rows (offset `0`). The first `m + 1` rows contain at least `m + 1` entries. -/
def a (m : ℕ) : ℕ := ((List.range (m + 1)).flatMap row).getD m 0

/-- The definition reproduces all 84 terms listed in OEIS (rows `0, …, 15`; kernel-checked). -/
theorem a_data : (List.range 84).map (fun i => a (i + 0)) =
    [1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 0, 1, 1, 0, 1, 2, 2, 0, 2, 1, 1, 1, 1, 1, 0, 0, 1, 2, 2,
      2, 0, 0, 2, 1, 2, 2, 1, 0, 1, 1, 2, 1, 2, 0, 1, 2, 2, 1, 0, 2, 1, 2, 1, 2, 1, 2, 0, 1, 0,
      2, 0, 2, 0, 1, 1, 1, 2, 0, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1] := by
  decide +kernel

/-- The entry's example rows `13`, `14`, `15` (kernel-checked). -/
theorem row_example : row 13 = [2, 0, 1, 0, 2, 0, 2, 0, 1] ∧
    row 14 = [1, 1, 2, 0, 1, 1, 1, 1, 2] ∧ row 15 = [2, 2, 1, 1, 2, 2, 2, 2, 1, 1] := by
  decide +kernel

/-- The entry of row `n` in column `k` (`k ≥ 1`): the `k`-th entry of row `n`, i.e. the base-3
digit of `2^n` at the place `3^(k-1)`. It is an actual entry of the triangle iff
`k ≤ (row n).length`. -/
def T (n k : ℕ) : ℕ := (row n).getD (k - 1) 0

/-- Column `1` (starting at row `0`) begins `1, 2, 1, 2, …` (kernel-checked). -/
theorem col1_data : (List.range 12).map (fun i => T i 1) = [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2] ∧
    1 ≤ (row 0).length := by
  decide +kernel

/-- Column `2` starts at row `2` and begins `1, 2, 2, 1, 0, 0, 1, 2, 2, 1, 0, 0`
(kernel-checked). -/
theorem col2_data : (row 1).length < 2 ∧ 2 ≤ (row 2).length ∧
    (List.range 12).map (fun i => T (i + 2) 2) = [1, 2, 2, 1, 0, 0, 1, 2, 2, 1, 0, 0] := by
  decide +kernel

/-- Column `3` starts at row `4` (kernel-checked). -/
theorem col3_data : (row 3).length < 3 ∧ 3 ≤ (row 4).length ∧
    (List.range 20).map (fun i => T (i + 4) 3) =
      [1, 0, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0] := by
  decide +kernel

/-- `q` is a period of column `k`: for every row `n` having an entry in column `k`, the entry
of row `n + q` in column `k` is the same. -/
def IsColPeriod (k q : ℕ) : Prop :=
  ∀ n : ℕ, k ≤ (row n).length → T (n + q) k = T n k

/-- The conjectured period `p(k) = 2*3^(k-1) = A008776(k-1)` of column `k`. -/
def p (k : ℕ) : ℕ := 2 * 3 ^ (k - 1)

/-- Finite sanity check of the conjectured behaviour for columns `2` and `3` (not part of the
statement): `p 2 = 6` and `p 3 = 18` are periods on the first rows checked, and the first
period of each column contains each digit `0, 1, 2` equally often (kernel-checked). -/
theorem sanity_small_columns :
    p 2 = 6 ∧ p 3 = 18 ∧
    (List.range 40).all (fun i => T (i + 2 + 6) 2 == T (i + 2) 2) = true ∧
    (List.range 40).all (fun i => T (i + 4 + 18) 3 == T (i + 4) 3) = true ∧
    (List.range 3).map (fun d => ((List.range 6).filter (fun i => T (i + 2) 2 == d)).length) =
      [2, 2, 2] ∧
    (List.range 3).map (fun d => ((List.range 18).filter (fun i => T (i + 4) 3 == d)).length) =
      [6, 6, 6] := by
  decide +kernel

/-- Conjecture 1 (L. Edson Jeffery, 2015): for every `k ≥ 1`, column `k` is periodic with
(least) period `p(k) = 2*3^(k-1)`; and for every `k > 1`, in each period of column `k` (every
block of `p(k)` consecutive terms of the column) the digits `0`, `1`, `2` occur equally
often. -/
def statement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (IsColPeriod k (p k) ∧ ∀ q : ℕ, 0 < q → q < p k → ¬ IsColPeriod k q) ∧
    (2 ≤ k → ∀ m : ℕ, k ≤ (row m).length → ∀ d e : ℕ, d < 3 → e < 3 →
      ((Finset.Ico m (m + p k)).filter (fun n => T n k = d)).card =
        ((Finset.Ico m (m + p k)).filter (fun n => T n k = e)).card)

end Math0.Statements.A265210
