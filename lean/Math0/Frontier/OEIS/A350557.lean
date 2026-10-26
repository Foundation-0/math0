/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A350557
import Math0.Audit

/-!
# OEIS A350557: the signed triangle is the inverse of A350512

We prove Werner Schulte's conjecture: `M(n,k) = (-1)^(n-k) T(n,k)` is the matrix inverse of the
lower-triangular matrix `L` of A350512, i.e. `L * M = I` and `M * L = I`.

Idea. Introduce two auxiliary lower-triangular matrices: the bidiagonal `A` with `A(n,n) = 1`,
`A(n,n-1) = 2n-1`, and `B` with `B(0,0) = 1`, `B(n,k) = (-1)^(n-k) C(n-1,k-1)` for `n, k ≥ 1`.
* `A * M = B`: this is the recurrence `T(n+1,j) = (2n+1) T(n,j) + [j ≥ 1] C(n,j-1)`, which
  follows from the definition of `T` by splitting off the top term of the sum.
* `B * L = A`: using `L(k+1,j) = (2j+1) C(k,j) + [j ≥ 1] C(k,j-1)`, this reduces to binomial
  inversion `∑_k (-1)^(m-k) C(m,k) C(k,i) = [m = i]` (coefficient of `X^i` in
  `((X+1) - 1)^m`).
Hence, on every `N × N` upper-left block, `A (M L) = (A M) L = B L = A`; `A` has determinant `1`,
so `M L = I`, and then `L M = I` because these are square matrices over a field.
-/

namespace Math0.Frontier.A350557
open Math0.Statements.A350557

/-- The bidiagonal matrix with `1` on the diagonal and `2n-1` at `(n, n-1)`. -/
private def A (n k : ℕ) : ℚ := if n = k then 1 else if n = k + 1 then 2 * (n : ℚ) - 1 else 0

/-- `B(0,0) = 1`, `B(n,k) = (-1)^(n-k) C(n-1,k-1)` for `n, k ≥ 1`, and `0` otherwise. -/
private def B (n k : ℕ) : ℚ :=
  if n = 0 then (if k = 0 then 1 else 0)
  else if k = 0 then 0 else (-1) ^ (n - k) * ((n - 1).choose (k - 1) : ℚ)

/-- Upper-left `N × N` block of an `ℕ`-indexed matrix. -/
private def toMat (N : ℕ) (X : ℕ → ℕ → ℚ) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j => X i j

/-- Entries of the product of two blocks, when the left factor is lower triangular. -/
private lemma toMat_mul_apply (X Y : ℕ → ℕ → ℚ) (hX : ∀ n k, n < k → X n k = 0) (N : ℕ)
    (i j : Fin N) :
    (toMat N X * toMat N Y) i j = ∑ k ∈ Finset.range (i + 1), X i k * Y k j := by
  rw [Matrix.mul_apply]
  simp only [toMat, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => X i k * Y k j) N]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [hX _ _ (by omega), zero_mul]

/-- `L` is lower triangular. -/
private lemma L_lower : ∀ n k, n < k → L n k = 0 := by
  intro n k h; simp [L, h]

/-- `M` is lower triangular. -/
private lemma M_lower : ∀ n k, n < k → M n k = 0 := by
  intro n k h; simp [M, T, h]

/-- `A` is lower triangular. -/
private lemma A_lower : ∀ n k, n < k → A n k = 0 := by
  intro n k h; unfold A; rw [if_neg (by omega), if_neg (by omega)]

/-- `B` is lower triangular. -/
private lemma B_lower : ∀ n k, n < k → B n k = 0 := by
  intro n k h
  unfold B
  by_cases hn : n = 0
  · rw [if_pos hn, if_neg (by omega)]
  · rw [if_neg hn, if_neg (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- Binomial inversion: `∑_k (-1)^(m-k) C(m,k) C(k,i) = [m = i]`. -/
private lemma inv_pascal (m i : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (-1 : ℚ) ^ (m - k) * (m.choose k : ℚ) * (k.choose i : ℚ) =
      if m = i then 1 else 0 := by
  have h : ((Polynomial.X + 1 : Polynomial ℚ) + Polynomial.C (-1)) ^ m =
      ∑ k ∈ Finset.range (m + 1), (Polynomial.X + 1) ^ k *
        Polynomial.C ((-1 : ℚ) ^ (m - k) * (m.choose k : ℚ)) := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, map_pow, map_natCast]
    ring
  have h2 := congrArg (fun p => Polynomial.coeff p i) h
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Polynomial.coeff_X_add_one_pow] at h2
  rw [show (Polynomial.X + 1 : Polynomial ℚ) + Polynomial.C (-1) = Polynomial.X by
    simp [map_neg, map_one]] at h2
  rw [Polynomial.coeff_X_pow] at h2
  rw [Finset.sum_congr rfl (fun k _ => by ring :
    ∀ k ∈ Finset.range (m + 1), (-1 : ℚ) ^ (m - k) * (m.choose k : ℚ) * (k.choose i : ℚ) =
      (k.choose i : ℚ) * ((-1) ^ (m - k) * (m.choose k : ℚ))), ← h2]
  split_ifs <;> first | rfl | omega

/-- For `k ≥ 1` the summation formula for `T n k` holds for all `n`
(the sum is empty if `n < k`). -/
private lemma T_pos (n k : ℕ) (hk : k ≠ 0) :
    T n k = (∑ i ∈ Finset.Icc k n,
      ((i - 1).choose (k - 1) : ℚ) * 2 ^ i * i.factorial / (2 * i).factorial) *
      (2 * n).factorial / (2 ^ n * n.factorial) := by
  simp only [T, hk, if_false]
  split_ifs with h
  · rw [Finset.Icc_eq_empty (by omega)]; simp
  · rfl

/-- `(2m+2)! = (2m+2)(2m+1)(2m)!`. -/
private lemma fact_two_succ (m : ℕ) :
    ((2 * (m + 1)).factorial : ℚ) = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
  rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  push_cast; ring

/-- The recurrence `T(m+1,j) = (2m+1) T(m,j) + [j ≥ 1] C(m,j-1)`. -/
private lemma T_succ (m j : ℕ) :
    T (m + 1) j = (2 * m + 1) * T m j + (if j = 0 then 0 else ((m.choose (j - 1) : ℕ) : ℚ)) := by
  have hf := fact_two_succ m
  have h1 : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h3 : (2 * (m : ℚ) + 2) ≠ 0 := by positivity
  have h4 : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
  have h5 : ((m : ℚ) + 1) ≠ 0 := by positivity
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [T, Nat.not_lt_zero, if_false, if_true]
    rw [hf, Nat.factorial_succ]; push_cast; field_simp; ring
  · rw [if_neg (by omega), T_pos _ _ (by omega), T_pos _ _ (by omega)]
    rcases le_or_gt j (m + 1) with hjm | hjm
    · rw [Finset.sum_Icc_succ_top hjm, hf, Nat.factorial_succ]
      simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
    · rw [Finset.Icc_eq_empty (by omega), Finset.Icc_eq_empty (by omega),
        Nat.choose_eq_zero_of_lt (by omega)]
      simp

/-- The signed recurrence `M(m+1,j) + (2m+1) M(m,j) = B(m+1,j)`. -/
private lemma M_succ (m j : ℕ) : M (m + 1) j + (2 * m + 1) * M m j = B (m + 1) j := by
  unfold M
  rw [T_succ]
  unfold B
  rw [if_neg (Nat.succ_ne_zero m)]
  rcases le_or_gt j m with hjm | hjm
  · rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ]
    split_ifs with hj
    · ring
    · simp only [Nat.add_sub_cancel]; ring
  · have hT : T m j = 0 := by simp [T, hjm]
    simp [hT, show j ≠ 0 by omega]

/-- `A * M = B`, entrywise. -/
private lemma AM_entry (n j : ℕ) : ∑ k ∈ Finset.range (n + 1), A n k * M k j = B n j := by
  cases n with
  | zero =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [A, M, B, T]
    · simp [A, M, B, T, hj, hj.ne']
  | succ m =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero, ← M_succ]
    · simp [A]; ring
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [A]
      rw [if_neg (by omega), if_neg (by omega), zero_mul]

/-- `L(k+1,j) = (2j+1) C(k,j) + [j ≥ 1] C(k,j-1)`. -/
private lemma L_succ (k j : ℕ) :
    L (k + 1) j = (2 * j + 1) * (k.choose j : ℚ) +
      (if j = 0 then 0 else (k.choose (j - 1) : ℚ)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [L]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [if_neg (Nat.succ_ne_zero i)]
    simp only [Nat.add_sub_cancel]
    rcases le_or_gt i k with hik | hik
    · have hc := Nat.choose_succ_right_eq k i
      have hc' : (k.choose (i + 1) : ℚ) * (i + 1) = (k.choose i : ℚ) * ((k : ℚ) - i) := by
        rw [← Nat.cast_sub hik]; exact_mod_cast hc
      unfold L
      rw [if_neg (by omega), if_neg (Nat.succ_ne_zero i)]
      simp only [Nat.add_sub_cancel, Nat.add_sub_add_right]
      rw [Nat.cast_sub hik, div_eq_iff (by positivity)]
      push_cast
      linear_combination (-(2 * (i : ℚ) + 3)) * hc'
    · unfold L
      rw [if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt hik]
      simp

/-- `B * L = A`, entrywise. -/
private lemma BL_entry (n j : ℕ) : ∑ k ∈ Finset.range (n + 1), B n k * L k j = A n j := by
  cases n with
  | zero =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [A, B, L]
    · simp [A, B, L, hj, hj.ne, hj.ne']
  | succ m =>
    rw [Finset.sum_range_succ']
    have hB : ∀ k, B (m + 1) (k + 1) = (-1) ^ (m - k) * (m.choose k : ℚ) := by
      intro k; simp [B]
    simp only [hB, L_succ]
    have e : ∀ k ∈ Finset.range (m + 1), (-1 : ℚ) ^ (m - k) * (m.choose k : ℚ) *
        ((2 * j + 1) * (k.choose j : ℚ) + (if j = 0 then 0 else (k.choose (j - 1) : ℚ))) =
        (2 * j + 1) * ((-1 : ℚ) ^ (m - k) * (m.choose k : ℚ) * (k.choose j : ℚ)) +
        (if j = 0 then 0 else 1) * ((-1 : ℚ) ^ (m - k) * (m.choose k : ℚ) *
          (k.choose (j - 1) : ℚ)) := by
      intro k _; split_ifs <;> ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      inv_pascal, inv_pascal, show B (m + 1) 0 = 0 by simp [B]]
    unfold A
    split_ifs <;> (try subst_vars) <;> first | omega | (push_cast; ring)

/-- `A * M = B` on `N × N` blocks. -/
private lemma mat_AM (N : ℕ) : toMat N A * toMat N M = toMat N B := by
  ext i j
  rw [toMat_mul_apply _ _ A_lower, AM_entry]
  rfl

/-- `B * L = A` on `N × N` blocks. -/
private lemma mat_BL (N : ℕ) : toMat N B * toMat N L = toMat N A := by
  ext i j
  rw [toMat_mul_apply _ _ B_lower, BL_entry]
  rfl

/-- The block of `A` is unitriangular, so its determinant is `1`. -/
private lemma det_A (N : ℕ) : (toMat N A).det = 1 := by
  have h : (toMat N A).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp only [toMat, Matrix.of_apply]
    exact A_lower _ _ hij'
  rw [Matrix.det_of_isLowerTriangular _ h]
  simp [toMat, A]

/-- `M * L = 1` on `N × N` blocks. -/
private lemma mat_ML (N : ℕ) : toMat N M * toMat N L = 1 := by
  have hu : IsUnit (toMat N A) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_A]; exact isUnit_one
  apply hu.mul_left_cancel
  rw [← mul_assoc, mat_AM, mat_BL, mul_one]

/-- `L * M = 1` on `N × N` blocks. -/
private lemma mat_LM (N : ℕ) : toMat N L * toMat N M = 1 := mul_eq_one_comm.mp (mat_ML N)

/-- Schulte's conjecture holds: `M(n,k) = (-1)^(n-k) T(n,k)` is the two-sided matrix inverse of
the triangle `L` of A350512. -/
theorem result : statement := by
  refine ⟨fun n j => ?_, fun n j => ?_⟩
  · have h : (toMat (n + j + 1) L * toMat (n + j + 1) M) ⟨n, by omega⟩ ⟨j, by omega⟩ =
        (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) ℚ) ⟨n, by omega⟩ ⟨j, by omega⟩ := by
      rw [mat_LM]
    rw [toMat_mul_apply _ _ L_lower, Matrix.one_apply] at h
    simpa [Fin.ext_iff] using h
  · have h : (toMat (n + j + 1) M * toMat (n + j + 1) L) ⟨n, by omega⟩ ⟨j, by omega⟩ =
        (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) ℚ) ⟨n, by omega⟩ ⟨j, by omega⟩ := by
      rw [mat_ML]
    rw [toMat_mul_apply _ _ M_lower, Matrix.one_apply] at h
    simpa [Fin.ext_iff] using h

end Math0.Frontier.A350557

#math0_settles Math0.Frontier.A350557.result Math0.Statements.A350557.statement
