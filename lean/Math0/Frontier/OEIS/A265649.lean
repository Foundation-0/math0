/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A265649
import Math0.Audit

/-!
# A265649: both closed forms of Werner Schulte hold

We prove both conjectures of the entry for the triangle
`T(n,k) = T(n-1,k-1) + (2n-1+k)·T(n-1,k)`, `T(0,0) = 1`.

**Method (factoring the triangle).** Suppose `A` and `D` are lower triangular arrays with
`A(n+1,i) = A(n,i-1) + α(n,i)·A(n,i)` and `D(i+1,k) = D(i,k-1) + β(i,k)·D(i,k)`, and
`α(n,i) + β(i,k) = γ(n,k)` does not depend on `i`. Then `S(n,k) = ∑_i A(n,i)·D(i,k)` satisfies
`S(n+1,k) = S(n,k-1) + γ(n,k)·S(n,k)`: expand `A(n+1,i)`, shift the index in the
`A(n,i-1)` part, and use the recurrence of `D`. So `S` agrees with any array obeying this
recurrence and the same row `0`.

* *First form.* `A(n,i) = 2^(n-i)·n!·C(n,i)/i!` (`α = 2n+2+2i`) and
  `D(i,k) = (-1/2)^(i-k)·(2i-k)!/((i-k)!·k!)` (`β = k-2i-1`). Then `γ = 2n+1+k`, as for `T`.
  With `i = k+j` the summand `A(n,k+j)·D(k+j,k)` is exactly the `j`-th term of
  `2^(n-k)·(n-k)!·C(n,k)·(-1/4)^j·C(2j+k,j)·C(n,j+k)`.
* *Second form.* `A = A001497` (Bessel, `α = 2N+1-j`) and `D(j,k) = (j+1)!·C(j+1,k)/k!`
  (the unsigned Laguerre row `j+1`, `β = j+2+k`). Then `γ = 2N+3+k`, the recurrence of
  `N ↦ T(N+1,k)`, and `(-1)^k·A021009(j+1,k) = D(j,k)`.

Each recurrence of `A` and `D` is a one-line identity of factorials, or Pascal's rule together
with `C(n,i+1)·(i+1) = C(n,i)·(n-i)`.
-/

namespace Math0.Frontier.A265649
open Math0.Statements.A265649

/-- Pushing one step of a two-term row recurrence of `A` across a sum `∑ A(n+1,i) X(i)`. -/
private theorem shift_sum (A : ℕ → ℕ → ℚ) (α : ℕ → ℕ → ℚ) (n : ℕ) (X : ℕ → ℚ)
    (hA0 : A (n+1) 0 = α n 0 * A n 0)
    (hA : ∀ i, A (n+1) (i+1) = A n i + α n (i+1) * A n (i+1))
    (hz : A n (n+1) = 0) :
    ∑ i ∈ Finset.range (n+2), A (n+1) i * X i =
      ∑ i ∈ Finset.range (n+1), A n i * (X (i+1) + α n i * X i) := by
  have h1 : ∑ i ∈ Finset.range (n+2), A (n+1) i * X i =
      ∑ i ∈ Finset.range (n+1), A n i * X (i+1) +
        ∑ i ∈ Finset.range (n+2), α n i * A n i * X i := by
    rw [Finset.sum_range_succ' _ (n+1), Finset.sum_range_succ' (fun i => α n i * A n i * X i) (n+1)]
    simp only [hA, hA0, add_mul, Finset.sum_add_distrib]
    ring
  rw [h1, Finset.sum_range_succ (fun i => α n i * A n i * X i), hz]
  simp only [mul_zero, zero_mul, add_zero, mul_add, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intros; ring

/-- If `A` and `D` satisfy two-term recurrences with coefficients `α(n,i)` and `β(i,k)` with
`α(n,i) + β(i,k) = γ(n,k)`, then `∑_i A(n,i) D(i,k)` satisfies the recurrence of `U` with
coefficient `γ`; so it equals `U` once the rows `n = 0` agree. -/
private theorem matrix_induction (A D U α β γ : ℕ → ℕ → ℚ)
    (hA0 : ∀ n, A (n+1) 0 = α n 0 * A n 0)
    (hA : ∀ n i, A (n+1) (i+1) = A n i + α n (i+1) * A n (i+1))
    (hz : ∀ n, A n (n+1) = 0)
    (hD0 : ∀ i, D (i+1) 0 = β i 0 * D i 0)
    (hD : ∀ i k, D (i+1) (k+1) = D i k + β i (k+1) * D i (k+1))
    (hγ : ∀ n i k, α n i + β i k = γ n k)
    (hU0 : ∀ n, U (n+1) 0 = γ n 0 * U n 0)
    (hU : ∀ n k, U (n+1) (k+1) = U n k + γ n (k+1) * U n (k+1))
    (hbase : ∀ k, U 0 k = A 0 0 * D 0 k) :
    ∀ n k, U n k = ∑ i ∈ Finset.range (n+1), A n i * D i k := by
  intro n
  induction n with
  | zero => intro k; simp [hbase]
  | succ n ih =>
    intro k
    rw [shift_sum A α n _ (hA0 n) (hA n) (hz n)]
    cases k with
    | zero =>
      rw [hU0, ih 0, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [hD0, ← hγ n i 0]; ring
    | succ k =>
      rw [hU, ih k, ih (k+1), Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [hD, ← hγ n i (k+1)]; ring

/-- The unsigned Laguerre triangle `m!·C(m,k)/k!` (it vanishes for `k > m`). -/
private def Lp (m k : ℕ) : ℚ := (m.factorial : ℚ) * (m.choose k : ℚ) / (k.factorial : ℚ)

/-- `C(n,i+1)·(i+1) = C(n,i)·(n-i)` in `ℚ`, for all `n, i`. -/
private theorem choose_rel (n i : ℕ) :
    (n.choose (i+1) : ℚ) * (i+1) = n.choose i * ((n:ℚ) - i) := by
  rcases Nat.lt_or_ge n i with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have := Nat.choose_succ_right_eq n i
    rw [← Nat.cast_sub h]
    exact_mod_cast this

/-- Column `0` of `Lp`: `Lp(m+1,0) = (m+1)·Lp(m,0)`. -/
private theorem Lp_succ_zero (m : ℕ) : Lp (m+1) 0 = (m+1) * Lp m 0 := by
  simp [Lp, Nat.factorial_succ]

/-- The Laguerre recurrence `Lp(m+1,k+1) = Lp(m,k) + (m+2+k)·Lp(m,k+1)`. -/
private theorem Lp_succ_succ (m k : ℕ) :
    Lp (m+1) (k+1) = Lp m k + (m + 2 + k) * Lp m (k+1) := by
  have hr := choose_rel m k
  simp only [Lp, Nat.choose_succ_succ', Nat.factorial_succ]
  push_cast
  field_simp
  linear_combination -hr

/-- `Lp(m,k) = 0` for `k > m`. -/
private theorem Lp_eq_zero {m k : ℕ} (h : m < k) : Lp m k = 0 := by
  simp [Lp, Nat.choose_eq_zero_of_lt h]

/-! ### The first closed form -/

/-- The scaled Laguerre triangle `2^(n-i)·n!·C(n,i)/i!`. -/
private def A₁ (n i : ℕ) : ℚ := (2:ℚ) ^ n / (2:ℚ) ^ i * Lp n i

/-- The triangle `(-1/2)^(i-k)·(2i-k)!/((i-k)!·k!)` for `k ≤ i` (else `0`). -/
private def D₁ (i k : ℕ) : ℚ :=
  if k ≤ i then (-1/2 : ℚ) ^ (i - k) * ((2 * i - k).factorial : ℚ) /
    (((i - k).factorial : ℚ) * (k.factorial : ℚ)) else 0

/-- `A₁(n+1,0) = (2n+2)·A₁(n,0)`. -/
private theorem A₁_succ_zero (n : ℕ) :
    A₁ (n+1) 0 = (2 * (n:ℚ) + 2 + 2 * ((0:ℕ):ℚ)) * A₁ n 0 := by
  simp only [A₁, Lp_succ_zero, pow_succ]
  push_cast
  ring

/-- `A₁(n+1,i+1) = A₁(n,i) + (2n+2+2(i+1))·A₁(n,i+1)`. -/
private theorem A₁_succ_succ (n i : ℕ) :
    A₁ (n+1) (i+1) = A₁ n i + (2 * (n:ℚ) + 2 + 2 * ((i+1:ℕ):ℚ)) * A₁ n (i+1) := by
  simp only [A₁, Lp_succ_succ, pow_succ]
  push_cast
  field_simp
  ring

/-- `A₁(n,n+1) = 0`. -/
private theorem A₁_zero (n : ℕ) : A₁ n (n+1) = 0 := by
  simp [A₁, Lp_eq_zero (Nat.lt_succ_self n)]

/-- `D₁(i+1,0) = -(2i+1)·D₁(i,0)`. -/
private theorem D₁_succ_zero (i : ℕ) :
    D₁ (i+1) 0 = (((0:ℕ):ℚ) - 2 * (i:ℚ) - 1) * D₁ i 0 := by
  unfold D₁
  rw [if_pos (Nat.zero_le _), if_pos (Nat.zero_le _)]
  have e : 2 * (i+1) - 0 = (2*i+1)+1 := by omega
  have e' : 2 * i - 0 = 2 * i := by omega
  rw [e, e', Nat.sub_zero, Nat.sub_zero]
  simp only [Nat.factorial_succ, Nat.factorial_zero]
  push_cast
  field_simp
  ring

/-- `D₁(i+1,k+1) = D₁(i,k) + ((k+1)-2i-1)·D₁(i,k+1)`. -/
private theorem D₁_succ_succ (i k : ℕ) :
    D₁ (i+1) (k+1) = D₁ i k + (((k+1:ℕ):ℚ) - 2 * (i:ℚ) - 1) * D₁ i (k+1) := by
  rcases lt_trichotomy k i with h | rfl | h
  · obtain ⟨m, rfl⟩ : ∃ m, i = k + m + 1 := ⟨i - k - 1, by omega⟩
    have h1 : k + 1 ≤ k + m + 1 + 1 := by omega
    have h2 : k ≤ k + m + 1 := by omega
    have h3 : k + 1 ≤ k + m + 1 := by omega
    unfold D₁
    rw [if_pos h1, if_pos h2, if_pos h3]
    have e1 : k + m + 1 + 1 - (k + 1) = m + 1 := by omega
    have e2 : 2 * (k + m + 1 + 1) - (k + 1) = (2 * m + k + 1) + 1 + 1 := by omega
    have e3 : k + m + 1 - k = m + 1 := by omega
    have e4 : 2 * (k + m + 1) - k = (2 * m + k + 1) + 1 := by omega
    have e5 : k + m + 1 - (k + 1) = m := by omega
    have e6 : 2 * (k + m + 1) - (k + 1) = 2 * m + k + 1 := by omega
    rw [e1, e2, e3, e4, e5, e6]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · unfold D₁
    rw [if_pos (le_refl _), if_pos (le_refl _), if_neg (by omega : ¬ (k + 1 ≤ k))]
    have e2 : 2 * (k + 1) - (k + 1) = k + 1 := by omega
    have e4 : 2 * k - k = k := by omega
    rw [e2, e4, Nat.sub_self, Nat.sub_self]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_zero, add_zero]
    rw [div_self (by positivity), div_self (by positivity)]
  · unfold D₁
    rw [if_neg (by omega : ¬ (k + 1 ≤ i + 1)), if_neg (by omega : ¬ (k ≤ i)),
      if_neg (by omega : ¬ (k + 1 ≤ i))]
    ring

/-- The defining recurrence of `T` in column `0`, cast to `ℚ`. -/
private theorem T_cast_succ_zero (n : ℕ) :
    (T (n+1) 0 : ℚ) = (2 * (n:ℚ) + 1 + ((0:ℕ):ℚ)) * T n 0 := by
  have e : T (n+1) 0 = (2 * n + 1) * T n 0 := by
    rw [T]; congr 1
  rw [e]; push_cast; ring

/-- The defining recurrence of `T` in columns `k+1`, cast to `ℚ`. -/
private theorem T_cast_succ_succ (n k : ℕ) :
    (T (n+1) (k+1) : ℚ) = T n k + (2 * (n:ℚ) + 1 + ((k+1:ℕ):ℚ)) * T n (k+1) := by
  have e : T (n+1) (k+1) = T n k + (2 * n + 1 + (k+1)) * T n (k+1) := by
    rw [T_succ_succ]; congr 2
  rw [e]; push_cast; ring

/-- `T = A₁ · D₁` as a product of lower triangular matrices. -/
private theorem stmt1_sum (n k : ℕ) :
    (T n k : ℚ) = ∑ i ∈ Finset.range (n+1), A₁ n i * D₁ i k := by
  refine matrix_induction A₁ D₁ (fun n k => (T n k : ℚ))
    (fun n i => 2 * (n:ℚ) + 2 + 2 * (i:ℚ)) (fun i k => (k:ℚ) - 2 * (i:ℚ) - 1)
    (fun n k => 2 * (n:ℚ) + 1 + (k:ℚ)) A₁_succ_zero A₁_succ_succ A₁_zero D₁_succ_zero
    D₁_succ_succ (fun n i k => by ring) T_cast_succ_zero T_cast_succ_succ ?_ n k
  intro k
  cases k with
  | zero => simp [A₁, D₁, Lp, T]
  | succ k => simp [A₁, D₁, T]

/-- The matrix product `A₁ · D₁` is the first closed form (reindex `i = k + j`). -/
private theorem sum_eq_rhs₁ (n k : ℕ) (hk : k ≤ n) :
    ∑ i ∈ Finset.range (n+1), A₁ n i * D₁ i k =
      2 ^ (n - k) * ((n - k).factorial : ℚ) * (n.choose k : ℚ) *
        ∑ j ∈ Finset.range (n - k + 1),
          (-1 / 4 : ℚ) ^ j * ((2 * j + k).choose j : ℚ) * (n.choose (j + k) : ℚ) := by
  have e : n + 1 = k + (n - k + 1) := by omega
  rw [e, Finset.sum_range_add, Finset.mul_sum]
  have h0 : ∑ i ∈ Finset.range k, A₁ n i * D₁ i k = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have : ¬ k ≤ i := by simp at hi; omega
    simp [D₁, this]
  rw [h0, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n - k := by simp at hj; omega
  obtain ⟨r, rfl⟩ : ∃ r, n = k + j + r := ⟨n - k - j, by omega⟩
  have hn : k + j + r - k = j + r := by omega
  have hfac := Nat.choose_mul_factorial_mul_factorial hk
  rw [hn] at hfac ⊢
  have hfacq : ((k + j + r).factorial : ℚ) =
      ((k + j + r).choose k : ℚ) * (k.factorial : ℚ) * ((j + r).factorial : ℚ) := by
    exact_mod_cast hfac.symm
  have hc : ((2 * j + k).choose j : ℚ) =
      ((2 * j + k).factorial : ℚ) / ((j.factorial : ℚ) * ((j + k).factorial : ℚ)) := by
    have e : 2 * j + k - j = j + k := by omega
    rw [Nat.cast_choose ℚ (by omega : j ≤ 2 * j + k), e]
  have hD : D₁ (k + j) k = (-1/2 : ℚ) ^ j * ((2 * j + k).factorial : ℚ) /
      ((j.factorial : ℚ) * (k.factorial : ℚ)) := by
    unfold D₁
    rw [if_pos (by omega)]
    have e1 : k + j - k = j := by omega
    have e2 : 2 * (k + j) - k = 2 * j + k := by omega
    rw [e1, e2]
  have hpow : (-1/2 : ℚ) ^ j = 2 ^ j * (-1/4) ^ j := by
    rw [← mul_pow]; norm_num
  rw [hD, hc, hpow]
  simp only [A₁, Lp]
  rw [hfacq, add_comm j k, pow_add, pow_add, pow_add]
  field_simp


/-! ### The second closed form -/

/-- `A001497(N+1,0) = (2N+1)·A001497(N,0)`. -/
private theorem B_succ_zero (N : ℕ) :
    A001497 (N+1) 0 = (2 * (N:ℚ) + 1 - ((0:ℕ):ℚ)) * A001497 N 0 := by
  unfold A001497
  rw [if_pos (Nat.zero_le _), if_pos (Nat.zero_le _)]
  have e1 : 2 * (N + 1) - 0 = (2 * N + 1) + 1 := by omega
  have e2 : 2 * N - 0 = 2 * N := by omega
  rw [e1, e2, Nat.sub_zero, Nat.sub_zero]
  simp only [Nat.factorial_succ, Nat.factorial_zero, pow_succ]
  push_cast
  field_simp
  ring

/-- `A001497(N+1,j+1) = A001497(N,j) + (2N+1-(j+1))·A001497(N,j+1)`. -/
private theorem B_succ_succ (N j : ℕ) :
    A001497 (N+1) (j+1) = A001497 N j + (2 * (N:ℚ) + 1 - ((j+1:ℕ):ℚ)) * A001497 N (j+1) := by
  rcases lt_trichotomy j N with h | rfl | h
  · obtain ⟨m, rfl⟩ : ∃ m, N = j + m + 1 := ⟨N - j - 1, by omega⟩
    unfold A001497
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have e1 : 2 * (j + m + 1 + 1) - (j + 1) = (j + 2 * m + 1) + 1 + 1 := by omega
    have e2 : j + m + 1 + 1 - (j + 1) = m + 1 := by omega
    have e3 : 2 * (j + m + 1) - j = (j + 2 * m + 1) + 1 := by omega
    have e4 : j + m + 1 - j = m + 1 := by omega
    have e5 : 2 * (j + m + 1) - (j + 1) = j + 2 * m + 1 := by omega
    have e6 : j + m + 1 - (j + 1) = m := by omega
    rw [e1, e2, e3, e4, e5, e6]
    simp only [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
    ring
  · unfold A001497
    rw [if_pos (le_refl _), if_pos (le_refl _), if_neg (by omega : ¬ (j + 1 ≤ j))]
    have e1 : 2 * (j + 1) - (j + 1) = j + 1 := by omega
    have e3 : 2 * j - j = j := by omega
    rw [e1, e3, Nat.sub_self, Nat.sub_self]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, mul_zero, add_zero]
    rw [div_self (by positivity), div_self (by positivity)]
  · unfold A001497
    rw [if_neg (by omega : ¬ (j + 1 ≤ N + 1)), if_neg (by omega : ¬ (j ≤ N)),
      if_neg (by omega : ¬ (j + 1 ≤ N))]
    ring

/-- `A001497(N,N+1) = 0`. -/
private theorem B_zero (N : ℕ) : A001497 N (N+1) = 0 := by
  unfold A001497
  rw [if_neg (by omega)]

/-- `A021009(n,m) = (-1)^m·Lp(n,m)` for all `n, m`. -/
private theorem A021009_eq (n m : ℕ) : A021009 n m = (-1) ^ m * Lp n m := by
  unfold A021009 Lp
  split_ifs with h
  · ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- `T(N+1,k) = ∑_j A001497(N,j)·Lp(j+1,k)`. -/
private theorem stmt2_sum (N k : ℕ) :
    (T (N+1) k : ℚ) = ∑ j ∈ Finset.range (N+1), A001497 N j * Lp (j+1) k := by
  refine matrix_induction A001497 (fun j k => Lp (j+1) k) (fun N k => (T (N+1) k : ℚ))
    (fun N j => 2 * (N:ℚ) + 1 - (j:ℚ)) (fun j k => (j:ℚ) + 2 + (k:ℚ))
    (fun N k => 2 * (N:ℚ) + 3 + (k:ℚ)) B_succ_zero B_succ_succ B_zero ?_ ?_
    (fun N j k => by ring) ?_ ?_ ?_ N k
  · intro j
    rw [Lp_succ_zero (j+1)]; push_cast; ring
  · intro j k
    rw [Lp_succ_succ (j+1) k]; push_cast; ring
  · intro N
    rw [T_cast_succ_zero (N+1)]; push_cast; ring
  · intro N k
    rw [T_cast_succ_succ (N+1) k]; push_cast; ring
  · intro k
    match k with
    | 0 => simp [A001497, Lp, T]
    | 1 => simp [A001497, Lp, T]
    | k + 2 =>
      rw [Lp_eq_zero (by omega)]
      simp [T]

/-- Both conjectures of Werner Schulte for A265649 hold. -/
theorem result : statement := by
  refine ⟨fun n k hk => ?_, fun n k hn hk => ?_⟩
  · rw [stmt1_sum n k, sum_eq_rhs₁ n k hk]
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    rw [stmt2_sum N k, Nat.add_sub_cancel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [A021009_eq]
    have h1 : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-(A001497 N j * Lp (j + 1) k)) * h1

end Math0.Frontier.A265649

#math0_settles Math0.Frontier.A265649.result Math0.Statements.A265649.statement
