/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A350557: the signed triangle is the matrix inverse of A350512

Source: https://oeis.org/A350557, Werner Schulte, Jan 05 2022 (FORMULA section of the entry he
authored). Verbatim:
> Conjecture: M(n,k) = (-1)^(n-k) * T(n,k) is matrix inverse of A350512.

The entry (offset `0`, keyword `tabl`) is "Triangle T(n,k) read by rows with
T(n,0) = (2*n)! / (2^n * n!) for n >= 0 and
T(n,k) = (Sum_{i=k..n} binomial(i-1,k-1) * 2^i * i! / (2*i)!) * (2*n)! / (2^n * n!)
for 0 < k <= n."
A350512 (Werner Schulte, Jan 02 2022, offset `0`, keyword `tabl`) is "Triangle read by rows
with T(n,0) = 1 for n >= 0 and T(n,k) = binomial(n-1,k-1)*(2*k*(n-k) + n)/k for 0 < k <= n."

## Encoding

* *The triangles.* Both definitions involve divisions, so both triangles are encoded literally
  as rational-valued functions `T n k : ℚ` (A350557) and `L n k : ℚ` (A350512), using exactly the
  formulas of the two names (`/` is division in `ℚ`; `binomial(i-1,k-1)` and `n-k` only occur
  with `1 ≤ k ≤ i` resp. `k ≤ n`, so the natural-number subtractions there are exact). Outside
  the triangles (`k > n`) both are set to `0`: the triangles are the nonzero parts of infinite
  lower-triangular matrices, which is how "matrix inverse" is meant for them.
* *Data.* `T_data` checks, as rational numbers, all 45 listed terms of A350557 (rows
  `n = 0, …, 8`); in particular these values are integers. `L_data` checks all 66 listed terms of
  A350512 (rows `n = 0, …, 10`). The sequence `a` (offset `0`) is A350557 read by rows, with the
  rational entries converted to `ℕ` by `⌊·⌋₊` (the entries are nonnegative integers, so this is
  the identity on them; `T_data` shows this on the listed range); `a_data` checks `a 0, …, a 44`.
* *The conjecture.* `M n k = (-1)^(n-k) * T n k` (with `M n k = 0` for `k > n`, as `T n k = 0`
  there). For lower-triangular infinite matrices the products are finite: the `(n, j)` entry of
  `L * M` is `∑_{k=0}^{n} L(n,k) M(k,j)`, since `L(n,k) = 0` for `k > n`, and similarly for
  `M * L`. "M is the matrix inverse of L" is encoded as `L * M = I` and `M * L = I`, i.e. for all
  `n, j ≥ 0` both sums equal `1` if `n = j` and `0` otherwise. (Equivalently: for every `N`, the
  `N × N` upper-left blocks of `L` and `M` are mutually inverse matrices.) `statement_check`
  confirms both identities for `n, j < 12` (a sanity check of the transcription, not a proof).
-/

namespace Math0.Statements.A350557

/-- A350557: `T(n,0) = (2n)! / (2^n n!)` and, for `0 < k ≤ n`,
`T(n,k) = (∑_{i=k}^{n} binomial(i-1,k-1) · 2^i · i! / (2i)!) · (2n)! / (2^n n!)`;
`T(n,k) = 0` outside the triangle (`k > n`). Computed in `ℚ`, literally as in the name. -/
def T (n k : ℕ) : ℚ :=
  if n < k then 0
  else if k = 0 then ((2 * n).factorial : ℚ) / (2 ^ n * n.factorial)
  else (∑ i ∈ Finset.Icc k n,
      ((i - 1).choose (k - 1) : ℚ) * 2 ^ i * i.factorial / (2 * i).factorial) *
    (2 * n).factorial / (2 ^ n * n.factorial)

/-- A350512: `L(n,0) = 1` and, for `0 < k ≤ n`, `L(n,k) = binomial(n-1,k-1) · (2k(n-k) + n) / k`;
`L(n,k) = 0` outside the triangle (`k > n`). Computed in `ℚ`, literally as in the name. -/
def L (n k : ℕ) : ℚ :=
  if n < k then 0
  else if k = 0 then 1
  else ((n - 1).choose (k - 1) : ℚ) * (2 * k * (n - k : ℕ) + n) / k

/-- The signed triangle `M(n,k) = (-1)^(n-k) · T(n,k)` of the conjecture. -/
def M (n k : ℕ) : ℚ := (-1) ^ (n - k) * T n k

/-! ### Data -/

/-- The definition of `T` reproduces all 45 listed terms of A350557 (rows `n = 0, …, 8`) exactly,
as rational numbers (kernel-checked). -/
theorem T_data : (List.range 9).map (fun n => (List.range (n + 1)).map (T n)) =
    [[1],
     [1, 1],
     [3, 4, 1],
     [15, 21, 7, 1],
     [105, 148, 52, 10, 1],
     [945, 1333, 472, 96, 13, 1],
     [10395, 14664, 5197, 1066, 153, 16, 1],
     [135135, 190633, 67567, 13873, 2009, 223, 19, 1],
     [2027025, 2859496, 1013512, 208116, 30170, 3380, 306, 22, 1]] := by
  decide +kernel

/-- The definition of `L` reproduces all 66 listed terms of A350512 (rows `n = 0, …, 10`) exactly,
as rational numbers (kernel-checked). -/
theorem L_data : (List.range 11).map (fun n => (List.range (n + 1)).map (L n)) =
    [[1],
     [1, 1],
     [1, 4, 1],
     [1, 7, 7, 1],
     [1, 10, 18, 10, 1],
     [1, 13, 34, 34, 13, 1],
     [1, 16, 55, 80, 55, 16, 1],
     [1, 19, 81, 155, 155, 81, 19, 1],
     [1, 22, 112, 266, 350, 266, 112, 22, 1],
     [1, 25, 148, 420, 686, 686, 420, 148, 25, 1],
     [1, 28, 189, 624, 1218, 1512, 1218, 624, 189, 28, 1]] := by
  decide +kernel

/-- A350557 as a sequence (offset `0`): the triangle `T` read by rows, entries converted to `ℕ`
by `⌊·⌋₊`. (Rows `0, …, i` contain at least `i + 1` entries, so the `i`-th entry of the
concatenation lies among them.) -/
def a (i : ℕ) : ℕ :=
  ((List.range (i + 1)).flatMap fun n => (List.range (n + 1)).map fun k => ⌊T n k⌋₊).getD i 0

/-- The definition reproduces all 45 terms listed in OEIS, `a 0, …, a 44` (kernel-checked). -/
theorem a_data : (List.range 45).map (fun i => a (i + 0)) =
    [1, 1, 1, 3, 4, 1, 15, 21, 7, 1, 105, 148, 52, 10, 1, 945, 1333, 472, 96, 13, 1, 10395,
      14664, 5197, 1066, 153, 16, 1, 135135, 190633, 67567, 13873, 2009, 223, 19, 1,
      2027025, 2859496, 1013512, 208116, 30170, 3380, 306, 22, 1] := by
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Werner Schulte, 2022): the lower-triangular matrix `M(n,k) = (-1)^(n-k) T(n,k)`
is the matrix inverse of the lower-triangular matrix `L` of A350512, i.e. `L * M = I` and
`M * L = I`: for all `n, j ≥ 0`, `∑_{k=0}^{n} L(n,k) M(k,j) = [n = j]` and
`∑_{k=0}^{n} M(n,k) L(k,j) = [n = j]` (the terms with `k > n` vanish since both matrices are
lower triangular). -/
def statement : Prop :=
  (∀ n j : ℕ, ∑ k ∈ Finset.range (n + 1), L n k * M k j = if n = j then 1 else 0) ∧
  (∀ n j : ℕ, ∑ k ∈ Finset.range (n + 1), M n k * L k j = if n = j then 1 else 0)

/-- Sanity check of the transcription (not a proof): both identities hold for `n, j < 12`. -/
theorem statement_check :
    (∀ n < 12, ∀ j < 12, ∑ k ∈ Finset.range (n + 1), L n k * M k j = if n = j then 1 else 0) ∧
    (∀ n < 12, ∀ j < 12, ∑ k ∈ Finset.range (n + 1), M n k * L k j = if n = j then 1 else 0) := by
  decide +kernel

end Math0.Statements.A350557
