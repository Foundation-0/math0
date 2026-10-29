/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A132616: Irwin's nested sums for column 0 of the odd-power triangle A132615

Source: https://oeis.org/A132616, Benedict W. J. Irwin, Nov 29 2016 (FORMULA section). Verbatim:
> Conjecture: a(n) is described by a series of nested sums,
> a(2) = Sum_{i=1..1} 1,
> a(3) = Sum_{i=1..1+2} Sum_{j=1..i} 1,
> a(4) = Sum_{i=1..1+4} Sum_{j=1..i+2} Sum_{k=1..j} 1,
> a(5) = Sum_{i=1..1+6} Sum_{j=1..i+4} Sum_{k=1..j+2} Sum_{l=1..k} 1,
> and so on, where 2, 4, 6,... are the even numbers.

The entry (Paul D. Hanna, Aug 24 2007; offset `0`) is "Column 0 of triangle A132615", and
A132615 (same author and date, offset `0`, keyword `tabl`) is "Triangle T, read by rows, where
row n+1 of T = row n of T^(2n-1) with appended '1' for n>=0 with T(0,0)=1."

## Encoding

* *The triangle.* `T` is the infinite lower-triangular matrix with `T(0,0) = 1` such that, for
  every `n ≥ 0`, row `n+1` of `T` is row `n` of `T^(2n-1)` (entries `0, …, n`) followed by
  `T(n+1,n+1) = 1` (and zeros after it). `tri n : Matrix (Fin (n+1)) (Fin (n+1)) ℕ` is the
  leading `(n+1) × (n+1)` block of `T` (rows and columns `0, …, n`), built row by row:
  `tri 0 = [[1]]`, and `tri (n+1)` is `tri n` bordered by a zero last column and by the last
  row `((tri n)^(2n-1))[n, 0..n] ++ [1]` (Mathlib's matrix power).
* *Why the truncation is faithful.* `tri n` is lower triangular (`tri_lower`), hence so is `T`,
  and the entry `(n, j)` of any power `T^e` only involves entries `T(i, l)` with
  `j ≤ l ≤ i ≤ n`; so row `n` of `T^e` is row `n` of `(tri n)^e`. Moreover `tri (n+1)` restricts
  to `tri n` on its first `n+1` rows and columns (`tri_succ_castSucc`), so all the blocks are
  consistent truncations of one infinite matrix `T`, given by `T n k` below.
* *The case `n = 0`.* There the exponent `2n-1 = -1` is negative: row `1` is row `0` of `T⁻¹`
  with a `1` appended. As `T` is lower unitriangular, row `0` of `T⁻¹` is `[1]` (followed by
  zeros), so row `1` is `[1, 1]`. In the code the exponent is the natural number `2 * n - 1`,
  which is `0` for `n = 0` (truncated subtraction); `(tri 0)^0 = [[1]]` has row `0` equal to
  `[1]` as well, so this is exactly the OEIS row `1`. (The `1 × 1` matrix `[[1]] = tri 0` has
  every integer power equal to `[[1]]`.)
* *Data.* `T_data` checks all 55 listed terms of A132615 (rows `0, …, 9`), and `a_data` checks
  all 19 listed terms `a(0), …, a(18)` of A132616 in the kernel, where `a n = T n 0`.
* *The nested sums.* For `m` nested sums with outer bound parameter `c`, write
  `nest m c = Sum_{i_1=1..c+2(m-1)} Sum_{i_2=1..i_1+2(m-2)} ⋯ Sum_{i_m=1..i_(m-1)+0} 1`;
  recursively `nest 0 c = 1` and `nest (m+1) c = Sum_{i=1..c+2m} nest m i`. Irwin's `a(n)` has
  `n - 1` nested sums whose upper limits add the even numbers `2(n-2), 2(n-3), …, 2, 0` to the
  previous index (to `1` for the outermost sum), i.e. it is `nest (n-1) 1`. The theorems
  `nest_two`, …, `nest_five` show that `nest (n-1) 1` is literally the displayed expression for
  `n = 2, 3, 4, 5` (`Finset.Icc 1 b` is `{1, …, b}`).
* *The conjecture.* `statement`: for every `n ≥ 2`, `a n = nest (n - 1) 1`. The displayed
  formulas start at `a(2)`, so `n ≥ 2` is the range of the conjecture. `statement_check` confirms
  the identity for `2 ≤ n ≤ 12` (a sanity check of the transcription, not a proof).
-/

namespace Math0.Statements.A132616

open Finset

/-- The leading `(n+1) × (n+1)` block of the triangle A132615 (rows and columns `0, …, n`):
`tri 0 = [[1]]`, and `tri (n+1)` keeps `tri n` in rows `0, …, n` (with a `0` in the new column
`n+1`), while its last row `n+1` is row `n` of `(tri n)^(2n-1)` with a `1` appended. -/
def tri : (n : ℕ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℕ
  | 0 => 1
  | n + 1 => Matrix.of fun i j =>
      if hi : (i : ℕ) ≤ n then
        if hj : (j : ℕ) ≤ n then tri n ⟨i, Nat.lt_succ_of_le hi⟩ ⟨j, Nat.lt_succ_of_le hj⟩
        else 0
      else
        if hj : (j : ℕ) ≤ n then (tri n ^ (2 * n - 1)) (Fin.last n) ⟨j, Nat.lt_succ_of_le hj⟩
        else 1

/-- The triangle A132615: `T n k` for `0 ≤ k ≤ n` (and `0` above the diagonal). -/
def T (n k : ℕ) : ℕ :=
  if h : k ≤ n then tri n (Fin.last n) ⟨k, Nat.lt_succ_of_le h⟩ else 0

/-- A132616: column `0` of the triangle A132615, `a(n) = T(n, 0)`. -/
def a (n : ℕ) : ℕ := T n 0

/-- `tri n` is lower triangular. -/
theorem tri_lower : ∀ (n : ℕ) (i j : Fin (n + 1)), (i : ℕ) < j → tri n i j = 0
  | 0, i, j, h => by omega
  | n + 1, i, j, h => by
    simp only [tri, Matrix.of_apply]
    split_ifs with hi hj hj
    · exact tri_lower n _ _ h
    · rfl
    · omega
    · omega

/-- `tri (n+1)` restricts to `tri n` on rows and columns `0, …, n`. -/
theorem tri_succ_castSucc (n : ℕ) (i j : Fin (n + 1)) :
    tri (n + 1) i.castSucc j.castSucc = tri n i j := by
  simp [tri, Fin.is_le]

/-- The definition reproduces the 55 listed terms of the triangle A132615 (rows `0, …, 9`,
read by rows; kernel-checked). -/
theorem T_data : ((List.range 10).flatMap fun n => (List.range (n + 1)).map fun k => T n k) =
    [1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 80, 25, 5, 1, 1, 1666, 378, 56, 7, 1, 1, 47232, 8460, 1020, 99,
      9, 1, 1, 1694704, 252087, 26015, 2134, 154, 11, 1, 1, 73552752, 9392890, 855478,
      61919, 3848, 221, 13, 1, 1, 3744491970, 420142350, 34461260, 2257413, 125760, 6290, 300,
      15, 1, 1] := by
  decide +kernel

/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all 19 listed
terms `a(0), …, a(18)`. -/
theorem a_data : (List.range 19).map (fun i => a (i + 0)) =
    [1, 1, 1, 6, 80, 1666, 47232, 1694704, 73552752, 3744491970, 218684051648,
      14406896813608, 1056681951098592, 85379764462169382, 7534286318509305600,
      720884741940337283712, 74330131862002429961712, 8215901579822006354547330,
      969069489665924620416715008] := by
  decide +kernel

/-- Irwin's nested sums with `m` summation signs and outer parameter `c`:
`nest m c = Sum_{i_1=1..c+2(m-1)} Sum_{i_2=1..i_1+2(m-2)} ⋯ Sum_{i_m=1..i_(m-1)} 1`. -/
def nest : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, c => ∑ i ∈ Icc 1 (c + 2 * m), nest m i

/-- The displayed instance `a(2) = Sum_{i=1..1} 1`. -/
theorem nest_two : nest (2 - 1) 1 = ∑ _i ∈ Icc 1 1, 1 := rfl

/-- The displayed instance `a(3) = Sum_{i=1..1+2} Sum_{j=1..i} 1`. -/
theorem nest_three : nest (3 - 1) 1 = ∑ i ∈ Icc 1 (1 + 2), ∑ _j ∈ Icc 1 i, 1 := rfl

/-- The displayed instance `a(4) = Sum_{i=1..1+4} Sum_{j=1..i+2} Sum_{k=1..j} 1`. -/
theorem nest_four :
    nest (4 - 1) 1 = ∑ i ∈ Icc 1 (1 + 4), ∑ j ∈ Icc 1 (i + 2), ∑ _k ∈ Icc 1 j, 1 := rfl

/-- The displayed instance
`a(5) = Sum_{i=1..1+6} Sum_{j=1..i+4} Sum_{k=1..j+2} Sum_{l=1..k} 1`. -/
theorem nest_five : nest (5 - 1) 1 =
    ∑ i ∈ Icc 1 (1 + 6), ∑ j ∈ Icc 1 (i + 4), ∑ k ∈ Icc 1 (j + 2), ∑ _l ∈ Icc 1 k, 1 := rfl

/-- Irwin's conjecture (2016): for every `n ≥ 2`, `a(n)` (column `0` of A132615) equals the
`n - 1` nested sums `Sum_{i_1=1..1+2(n-2)} Sum_{i_2=1..i_1+2(n-3)} ⋯ Sum_{i_(n-1)=1..i_(n-2)} 1`. -/
def statement : Prop := ∀ n : ℕ, 2 ≤ n → a n = nest (n - 1) 1

/-- Sanity check of the transcription (not a proof): the identity holds for `2 ≤ n ≤ 12`. -/
theorem statement_check : ∀ n ∈ Icc 2 12, a n = nest (n - 1) 1 := by
  decide +kernel

end Math0.Statements.A132616
