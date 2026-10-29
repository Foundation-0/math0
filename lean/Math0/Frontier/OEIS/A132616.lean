/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A132616
import Math0.Audit

/-!
# Irwin's nested sums for column 0 of the triangle A132615

We prove Irwin's conjecture: for `n ≥ 2`, `a(n) = T(n, 0)` equals the `n - 1` nested sums
`Sum_{i_1=1..1+2(n-2)} Sum_{i_2=1..i_1+2(n-3)} ⋯ Sum_{i_(n-1)=1..i_(n-2)} 1`.

**The powers of `T`.** Define `N p n k` by `N p 0 k = [k = 0]` and
`N p (n+1) k = [k = n+1] + Sum_{i<p} N (2n-1+i) n k`. It is lower unitriangular, satisfies
`N 0 n k = [k = n]` and `N (p+1) (n+1) k = N p (n+1) k + N (2n-1+p) n k`.

**Semigroup law.** `Sum_{m ≤ n} N p n m * N q m k = N (p+q) n k`, by induction on `n` and then
on `p`: the increment in `p` of the left side is `Sum_{m ≤ n-1} N (2n-3+p) (n-1) m * N q m k`,
which by the induction hypothesis on `n` is `N (2n-3+p+q) (n-1) k`, the increment in `p` of
the right side.

**Identification with `T`.** Hence if `tri n` has entries `N 1 i j`, then `(tri n)^e` has
entries `N e i j`. By induction on `n`, `tri n` has entries `N 1 i j`: the new last row of
`tri (n+1)` is row `n` of `(tri n)^(2n-1)`, i.e. `N (2n-1) n j = N 1 (n+1) j`.

**The nested sums.** Unfolding the recursion, `nest m c = N (c + 2m - 2) m 0`, and
`a(n+1) = N 1 (n+1) 0 = N (2n-1) n 0 = nest n 1` for `n ≥ 1`.
-/

namespace Math0.Frontier.A132616
open Math0.Statements.A132616
open Finset

/-- The entries of the powers of `T`: `N p n k = (T^p)(n, k)`. -/
private def N : ℕ → ℕ → ℕ → ℕ
  | _, 0, k => if k = 0 then 1 else 0
  | p, n + 1, k => (if k = n + 1 then 1 else 0) + ∑ i ∈ range p, N (2 * n - 1 + i) n k

/-- Unfolding `N` on a successor row. -/
private lemma N_succ (p n k : ℕ) :
    N p (n + 1) k = (if k = n + 1 then 1 else 0) + ∑ i ∈ range p, N (2 * n - 1 + i) n k := by
  rw [N]

/-- Row `0` of `N` does not depend on the exponent. -/
private lemma N_zero_row (p k : ℕ) : N p 0 k = if k = 0 then 1 else 0 := by
  rw [N]

/-- The increment of `N` in the exponent. -/
private lemma N_step (p n k : ℕ) :
    N (p + 1) (n + 1) k = N p (n + 1) k + N (2 * n - 1 + p) n k := by
  rw [N_succ, N_succ, sum_range_succ, add_assoc]

/-- `N` is lower triangular. -/
private lemma N_upper : ∀ (p n k : ℕ), n < k → N p n k = 0
  | p, 0, k, h => by rw [N_zero_row, if_neg (by omega)]
  | p, n + 1, k, h => by
    rw [N_succ, if_neg (by omega), zero_add]
    exact sum_eq_zero fun i _ => N_upper _ n k (by omega)

/-- `N` has ones on the diagonal. -/
private lemma N_diag : ∀ p n, N p n n = 1
  | p, 0 => by rw [N_zero_row, if_pos rfl]
  | p, n + 1 => by
    rw [N_succ, if_pos rfl, sum_eq_zero fun i _ => N_upper _ n (n + 1) (by omega), add_zero]

/-- The exponent `0` gives the identity matrix. -/
private lemma N_zero_left : ∀ n k, N 0 n k = if k = n then 1 else 0
  | 0, k => by rw [N_zero_row]
  | n + 1, k => by rw [N_succ, sum_range_zero, add_zero]

/-- The semigroup law `N p * N q = N (p + q)`. -/
private lemma N_mul : ∀ n p q k, ∑ m ∈ range (n + 1), N p n m * N q m k = N (p + q) n k
  | 0, p, q, k => by
    rw [sum_range_one, N_zero_row, if_pos rfl, one_mul, N_zero_row, N_zero_row]
  | n + 1, p, q, k => by
    induction p with
    | zero =>
      rw [sum_range_succ, sum_eq_zero fun m hm => by
        rw [N_zero_left, if_neg (by simp at hm; omega), zero_mul]]
      rw [N_zero_left, if_pos rfl, one_mul, zero_add, zero_add]
    | succ p ih =>
      have h1 : ∑ m ∈ range (n + 1 + 1), N (p + 1) (n + 1) m * N q m k =
          ∑ m ∈ range (n + 1 + 1), N p (n + 1) m * N q m k +
            ∑ m ∈ range (n + 1 + 1), N (2 * n - 1 + p) n m * N q m k := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun m _ => by rw [N_step, add_mul]
      have h2 : ∑ m ∈ range (n + 1 + 1), N (2 * n - 1 + p) n m * N q m k =
          N (2 * n - 1 + p + q) n k := by
        rw [sum_range_succ, N_upper _ n (n + 1) (by omega), zero_mul, add_zero]
        exact N_mul n _ q k
      rw [h1, ih, h2, show p + 1 + q = (p + q) + 1 by omega, N_step, add_assoc]

/-- If `tri n` has entries `N 1`, then its `e`-th power has entries `N e`. -/
private lemma tri_pow_of (n : ℕ) (h : ∀ i j : Fin (n + 1), tri n i j = N 1 i j) :
    ∀ e (i j : Fin (n + 1)), (tri n ^ e) i j = N e i j := by
  intro e
  induction e with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply, N_zero_left]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h' => hij (Fin.ext h'.symm))]
  | succ e ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    simp only [ih, h]
    rw [Fin.sum_univ_eq_sum_range (fun m => N e i m * N 1 m j) (n + 1)]
    have hi : (i : ℕ) + 1 ≤ n + 1 := i.isLt
    rw [← sum_range_add_sum_Ico _ hi, N_mul, sum_eq_zero fun m hm => by
      rw [N_upper e i m (by simp at hm; omega), zero_mul], add_zero]

/-- The truncations of the triangle have entries `N 1`. -/
private lemma tri_eq : ∀ n (i j : Fin (n + 1)), tri n i j = N 1 i j
  | 0, i, j => by
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi; subst hj
    rw [Fin.val_zero, N_diag]
    rfl
  | n + 1, i, j => by
    simp only [tri, Matrix.of_apply]
    split_ifs with hi hj hj
    · exact tri_eq n _ _
    · rw [N_upper]; omega
    · rw [tri_pow_of n (tri_eq n), Fin.val_last]
      have hi' : (i : ℕ) = n + 1 := by omega
      rw [hi', N_succ, if_neg (by omega), zero_add, sum_range_one, add_zero]
    · have hi' : (i : ℕ) = n + 1 := by omega
      have hj' : (j : ℕ) = n + 1 := by omega
      rw [hi', hj', N_diag]

/-- `a n = N 1 n 0`. -/
private lemma a_eq (n : ℕ) : a n = N 1 n 0 := by
  unfold a T
  rw [dif_pos (Nat.zero_le n), tri_eq, Fin.val_last]

/-- Irwin's nested sums in terms of `N`. -/
private lemma nest_eq : ∀ m c, nest m c = N (c + 2 * m - 2) m 0
  | 0, c => by rw [nest, N_zero_row, if_pos rfl]
  | m + 1, c => by
    rw [nest, show c + 2 * (m + 1) - 2 = c + 2 * m by omega, N_succ, if_neg (by omega),
      zero_add, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
      show c + 2 * m + 1 - 1 = c + 2 * m by omega]
    refine sum_congr rfl fun i _ => ?_
    rw [nest_eq m (1 + i)]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [N_zero_row, N_zero_row]
    · congr 1; omega

/-- Irwin's conjecture holds. -/
theorem result : statement := by
  intro n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [a_eq, Nat.add_sub_cancel, nest_eq, N_succ, if_neg (by omega), zero_add, sum_range_one]
  congr 1
  omega

end Math0.Frontier.A132616

#math0_settles Math0.Frontier.A132616.result Math0.Statements.A132616.statement
