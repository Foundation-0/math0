/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A119936: row-LCM of the denominators of the cube of the mean matrix is `n³·(lcm(1..n)/n)²`

Source: https://oeis.org/A119936, Wolfdieter Lang, Jul 20 2006 (FORMULA section). Verbatim:
> a(n)/n^3 = A027451(n) = A002944(n)^2 (the second equation is a conjecture).

The entry (offset `1`) is named "Least common multiple (LCM) of denominators of the rows of the
triangle of rationals A119935/A119932", with the comment "The triangle of rationals is the
matrix cube of the matrix with elements a(i,j) = 1/i if j <= i, 0 if j > i" and the formula
"a(n) = lcm_{m=1..n} seq(A119932(n,m)), n >= 1". Here A119932(n,m) is the denominator of
`r(n,m) := (A^3)[n,m]` in lowest terms (A119935 is its numerator).

## Encoding

* *The matrix.* `A i j : ℚ` is `1/i` if `j ≤ i` and `0` otherwise (indices start at `1`).
  `Amat N` is its `N × N` leading truncation, as a Mathlib `Matrix (Fin N) (Fin N) ℚ` (the
  `Fin N` index `i` stands for the OEIS index `i + 1`).
* *The triangle.* `r n m` (`1 ≤ m ≤ n`) is the entry in row `n`, column `m` of `Amat n ^ 3`
  (Mathlib's matrix power). Since `A` is lower triangular, `(A^3)[n,m]` only involves indices
  `≤ n`, so this is the `(n,m)` entry of the cube of the infinite matrix; `r_eq_sum` and
  `r_eq_explicit` prove `r n m = ∑_{k,l=1}^{n} A(n,k) A(k,l) A(l,m)
  = (1/n) ∑_{m ≤ l ≤ k ≤ n} 1/(k l)`. `triangle_num_data` and `triangle_den_data` check, in the
  kernel, that `r` read by rows reproduces all listed terms of A119935 (numerators, 37 terms) and
  A119932 (denominators, 32 terms); `Rat.num`/`Rat.den` are in lowest terms.
* *The sequence.* `a n` is the LCM, over `m = 1, …, n`, of the denominators `(r n m).den`, as in
  the name and the formula above. `a_data` checks all 19 listed terms `a(1), …, a(19)` in the
  kernel.
* *The conjecture.* A027451 is "First diagonal of A027447", and A027447 lists row `n` of `A^3`
  written over the least common denominator, i.e. A027447(n,m) = a(n)·r(n,m) (this is the
  formula `A027447(i,j) = a(i)*A119935(i,j)/A119932(i,j)` of the entry). As `r(n,n) = 1/n³`,
  A027451(n) = a(n)/n³: this is the first, non-conjectural equation. The conjecture is the second
  equation, A027451(n) = A002944(n)², i.e. `a(n)/n³ = A002944(n)²`, where A002944 is
  "a(n) = LCM(1,2,...,n) / n" (offset `1`). `A002944 n` is `lcmUpTo n / n` with
  `lcmUpTo n = lcm(1, …, n)` (`Finset.lcm` over `[1, n]`); the division is exact for `n ≥ 1`
  (`A002944_mul`), and `A002944_data` checks the 31 listed terms of A002944.
  `statement` asserts `(a n : ℚ) / n³ = (A002944 n)²` in `ℚ` for every `n ≥ 1` (the common
  offset of A119936, A027451 and A002944). `statement_iff` shows it is equivalent to the integer
  identity `a n = n · lcm(1, …, n)²` for every `n ≥ 1`.
-/

namespace Math0.Statements.A119936

/-- The lower-triangular mean matrix (1-indexed): `A(i,j) = 1/i` if `j ≤ i`, `0` if `j > i`. -/
def A (i j : ℕ) : ℚ := if j ≤ i then 1 / (i : ℚ) else 0

/-- The `N × N` leading truncation of `A`; the index `i : Fin N` stands for row/column `i + 1`. -/
def Amat (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j => A ((i : ℕ) + 1) ((j : ℕ) + 1)

/-- The triangle of rationals A119935/A119932: `r n m = (A^3)[n,m]` for `1 ≤ m ≤ n`, computed as
the `(n,m)` entry of the cube of the `n × n` truncation of `A` (`0` outside the triangle). -/
def r (n m : ℕ) : ℚ :=
  if h : 1 ≤ m ∧ m ≤ n then (Amat n ^ 3) ⟨n - 1, by omega⟩ ⟨m - 1, by omega⟩ else 0

/-- A119936: the LCM of the (lowest-terms) denominators of row `n` of the triangle `r`,
`a(n) = lcm_{m=1..n} A119932(n,m)`. -/
def a (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm fun m => (r n m).den

/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all 19 listed
terms `a(1), …, a(19)`. -/
theorem a_data : (List.range 19).map (fun i => a (i + 1)) =
    [1, 8, 108, 576, 18000, 21600, 1234800, 5644800, 57153600, 63504000, 8452382400,
      9220780800, 1688171284800, 1818030614400, 1947889944000, 8310997094400,
      2551995545299200, 2702112930316800, 1029655143835718400] := by
  decide +kernel

/-! ### Sanity checks of the triangle -/

/-- Rows `1, …, K` of the triangle `r`, read by rows. -/
def triangle (K : ℕ) : List ℚ :=
  (List.range K).flatMap fun i => (List.range (i + 1)).map fun j => r (i + 1) (j + 1)

/-- The numerators of `r`, read by rows, are the 37 listed terms of A119935. -/
theorem triangle_num_data : ((triangle 9).take 37).map Rat.num =
    [1, 7, 1, 85, 19, 1, 415, 115, 37, 1, 12019, 3799, 1489, 61, 1, 13489, 4669, 2059, 919,
      91, 1, 726301, 268921, 128431, 64171, 7669, 127, 1, 3144919, 1227199, 621139,
      334699, 178669, 3565, 169, 1, 30300391] := by
  decide +kernel

/-- The denominators of `r`, read by rows, are the 32 listed terms of A119932. -/
theorem triangle_den_data : ((triangle 8).take 32).map Rat.den =
    [1, 8, 8, 108, 108, 27, 576, 576, 576, 64, 18000, 18000, 18000, 2000, 125, 21600,
      21600, 21600, 21600, 5400, 216, 1234800, 1234800, 1234800, 1234800, 308700,
      12348, 343, 5644800, 5644800, 5644800, 5644800] := by
  decide +kernel

theorem sum_fin_eq_sum_Icc (n : ℕ) (f : ℕ → ℚ) :
    ∑ i : Fin n, f ((i : ℕ) + 1) = ∑ k ∈ Finset.Icc 1 n, f k := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) n, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-- `r n m` is the matrix-cube entry `∑_{k,l=1}^{n} A(n,k) A(k,l) A(l,m)`. -/
theorem r_eq_sum {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    r n m = ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Icc 1 n, A n k * A k l * A l m := by
  rw [r, dif_pos ⟨hm, hmn⟩]
  simp only [pow_succ', pow_zero, mul_one, Matrix.mul_apply, Amat, Matrix.of_apply,
    Finset.mul_sum, ← mul_assoc]
  have h1 : n - 1 + 1 = n := by omega
  have h2 : m - 1 + 1 = m := by omega
  simp only [h1, h2]
  rw [← sum_fin_eq_sum_Icc n (fun k => ∑ l ∈ Finset.Icc 1 n, A n k * A k l * A l m)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum_fin_eq_sum_Icc n (fun l => A n (k + 1) * A (k + 1) l * A l m)

/-- Explicit form: `r(n,m) = (1/n) ∑_{m ≤ l ≤ k ≤ n} 1/(k l)`. -/
theorem r_eq_explicit {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    r n m = 1 / (n : ℚ) * ∑ k ∈ Finset.Icc m n, ∑ l ∈ Finset.Icc m k, 1 / ((k : ℚ) * l) := by
  rw [r_eq_sum hm hmn, Finset.mul_sum]
  have inner : ∀ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Icc 1 n, A n k * A k l * A l m
      = 1 / (n : ℚ) * ∑ l ∈ Finset.Icc m k, 1 / ((k : ℚ) * l) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mul_sum]
    have hsub : Finset.Icc m k ⊆ Finset.Icc 1 n := Finset.Icc_subset_Icc hm hk.2
    rw [← Finset.sum_subset hsub (f := fun l => A n k * A k l * A l m) ?_]
    · refine Finset.sum_congr rfl fun l hl => ?_
      rw [Finset.mem_Icc] at hl
      simp only [A, if_pos hk.2, if_pos hl.2, if_pos hl.1]
      ring
    · intro l _ hl'
      simp only [Finset.mem_Icc, not_and_or, not_le] at hl'
      simp only [A]
      rcases hl' with h | h
      · rw [if_neg (by omega : ¬ m ≤ l)]; simp
      · rw [if_neg (by omega : ¬ l ≤ k)]; simp
  rw [Finset.sum_congr rfl inner]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc hm le_rfl)
  intro k hk hk'
  simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
  have : Finset.Icc m k = ∅ := Finset.Icc_eq_empty (by omega)
  simp [this]

/-! ### A002944 and the conjecture -/

/-- `lcm(1, 2, …, n)` (A003418); `lcmUpTo 0 = 1`. -/
def lcmUpTo (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-- A002944: `LCM(1, 2, …, n) / n` (exact division for `n ≥ 1`, see `A002944_mul`). -/
def A002944 (n : ℕ) : ℕ := lcmUpTo n / n

theorem A002944_mul {n : ℕ} (hn : 1 ≤ n) : A002944 n * n = lcmUpTo n :=
  Nat.div_mul_cancel (Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩))

/-- `A002944` reproduces the 31 listed terms of A002944 (kernel-checked). -/
theorem A002944_data : (List.range 31).map (fun i => A002944 (i + 1)) =
    [1, 1, 2, 3, 12, 10, 60, 105, 280, 252, 2520, 2310, 27720, 25740, 24024, 45045, 720720,
      680680, 12252240, 11639628, 11085360, 10581480, 232792560, 223092870, 1070845776,
      1029659400, 2974571600, 2868336900, 80313433200, 77636318760, 2329089562800] := by
  decide +kernel

/-- The conjecture: for every `n ≥ 1`, `a(n)/n³ = A002944(n)²` (here `a(n)/n³` is A027451(n),
the diagonal entry `a(n)·r(n,n)` of A027447, so this is the conjectured
`A027451(n) = A002944(n)²`). -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n : ℚ) / (n : ℚ) ^ 3 = ((A002944 n : ℕ) : ℚ) ^ 2

/-- Equivalent integer form: `a(n) = n · lcm(1, …, n)²` for every `n ≥ 1`. -/
theorem statement_iff : statement ↔ ∀ n : ℕ, 1 ≤ n → a n = n * lcmUpTo n ^ 2 := by
  unfold statement
  refine forall_congr' fun n => imp_congr_right fun hn => ?_
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [← A002944_mul hn, div_eq_iff (pow_ne_zero 3 hn'), ← Nat.cast_inj (R := ℚ)]
  push_cast
  constructor <;> intro h <;> rw [h] <;> ring

end Math0.Statements.A119936
