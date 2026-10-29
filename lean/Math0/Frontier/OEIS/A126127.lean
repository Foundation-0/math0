/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A126127
import Math0.Audit

/-!
# A126127: the conjectured g.f. of the inverse square of A061554 holds

We prove Robert Israel's conjecture
`∑_{n,k} T(n,k) x^n y^k = (1-x)(1-x+x^2)/(1-xy+3x^2-x^3y+x^4)`, where `T = M^(-2)` and
`M(n,k) = binomial(n, floor((n-k)/2))` (A061554).

* The inverse `N = M⁻¹` is the Riordan array `((1-x)/(1+x^2), x/(1+x^2))`. We define it by its
  recurrence `N(n,k) + N(n-2,k) = N(n-1,k-1) + [k = 0]([n = 0] - [n = 1])` and check
  `M · N = 1` with the production matrix of `M`: the rows of `M` satisfy
  `M(n+1,k) = M(n,k-1) + M(n,k+1)` (`k ≥ 1`) and `M(n+1,0) = M(n,0) + M(n,1)` (Pascal's rule),
  and the same recurrence of `N` gives `N(i+1,k) + N(i-1,k) = N(i,k-1)` (with `N(-1,k)` read as
  `N(0,k)`), so row `n+1` of `M · N` is row `n` shifted one step right.
* With `W(m,k) = ∑_j N(m,j+1) N(j,k)`, the recurrence of `N` in both factors of
  `T = N · N` gives `T(n+2,k) + T(n,k) = T(n+1,k-1) - W(n+1,k) - [k = 0] N(n+1,0)` and
  `W(m+2,k) + W(m,k) = T(m+1,k)`. Adding the first identity at `n` and `n+2` and using the
  second gives `T(n+4,k) + 3T(n+2,k) + T(n,k) = T(n+3,k-1) + T(n+1,k-1)`, which is the
  denominator; rows `0..3` give the numerator `1 - 2x + 2x^2 - x^3`.
-/

namespace Math0.Frontier.A126127
open Math0.Statements.A126127
open Finset

/-- The explicit inverse of `M`, given by the recurrence
`N(n,k) + N(n-2,k) = N(n-1,k-1) + [k = 0]([n = 0] - [n = 1])`. -/
private def N : ℕ → ℕ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | 1, 0 => -1
  | 1, k + 1 => N 0 k
  | n + 2, 0 => -N n 0
  | n + 2, k + 1 => N (n + 1) k - N n (k + 1)

/-- Column-zero recurrence for `N`. -/
private theorem N_rec0 (n : ℕ) : N (n + 2) 0 + N n 0 = 0 := by
  simp [N]

/-- Main recurrence for `N`. -/
private theorem N_rec (n k : ℕ) : N (n + 2) (k + 1) + N n (k + 1) = N (n + 1) k := by
  simp [N]

/-- `N` is lower triangular. -/
private theorem N_eq_zero : ∀ n k, n < k → N n k = 0
  | 0, k, h => by simp [N]; omega
  | 1, 0, h => by omega
  | 1, k + 1, h => by simp [N]; omega
  | n + 2, 0, h => by omega
  | n + 2, k + 1, h => by
      simp only [N]
      rw [N_eq_zero (n + 1) k (by omega), N_eq_zero n (k + 1) (by omega)]
      simp

/-- Row recurrence of `M` (columns `≥ 1`). -/
private theorem M_succ_succ (n k : ℕ) : M (n + 1) (k + 1) = M n k + M n (k + 2) := by
  unfold M
  by_cases hk : k ≤ n
  · rw [if_pos (by omega), if_pos hk]
    have e1 : (n + 1 - (k + 1)) / 2 = (n - k) / 2 := by omega
    rw [e1]
    by_cases hk2 : k + 2 ≤ n
    · rw [if_pos hk2]
      have e2 : (n - k) / 2 = (n - (k + 2)) / 2 + 1 := by omega
      rw [e2, Nat.choose_succ_succ]
      push_cast
      ring
    · rw [if_neg hk2]
      have e2 : (n - k) / 2 = 0 := by omega
      rw [e2]
      simp
  · rw [if_neg (by omega), if_neg hk, if_neg (by omega)]
    simp

/-- Row recurrence of `M` (column `0`). -/
private theorem M_succ_zero (n : ℕ) : M (n + 1) 0 = M n 0 + M n 1 := by
  unfold M
  rcases Nat.even_or_odd' n with ⟨a, rfl | rfl⟩
  · rcases a with _ | a
    · simp
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      have e1 : (2 * (a + 1) + 1 - 0) / 2 = a + 1 := by omega
      have e2 : (2 * (a + 1) - 0) / 2 = a + 1 := by omega
      have e3 : (2 * (a + 1) - 1) / 2 = a := by omega
      rw [e1, e2, e3, Nat.choose_succ_succ]
      push_cast
      ring
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have e1 : (2 * a + 1 + 1 - 0) / 2 = a + 1 := by omega
    have e2 : (2 * a + 1 - 0) / 2 = a := by omega
    have e3 : (2 * a + 1 - 1) / 2 = a := by omega
    rw [e1, e2, e3, Nat.choose_succ_succ, Nat.choose_symm_half]
    push_cast
    ring

/-- `N(i-1,k)` for `i ≥ 1`, and `N(0,k)` for `i = 0`. -/
private def prevN (i k : ℕ) : ℤ :=
  match i with
  | 0 => N 0 k
  | i + 1 => N i k

/-- The production-matrix identity `P · N = N · Sᵀ`. -/
private theorem N_shift (i k : ℕ) :
    N (i + 1) k + prevN i k = if k = 0 then 0 else N i (k - 1) := by
  rcases i with _ | i <;> rcases k with _ | k
  · simp [N, prevN]
  · simp [N, prevN]
  · simp only [prevN, if_true]
    exact N_rec0 i
  · simp only [prevN, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero k)]
    exact N_rec i k

/-- `M · N = 1`, as a finite sum over any range `L > n`. -/
private theorem M_mul_N (n : ℕ) :
    ∀ L k, n < L → ∑ j ∈ range L, M n j * N j k = if n = k then 1 else 0 := by
  induction n with
  | zero =>
    intro L k hL
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [sum_range_succ', sum_eq_zero (fun j _ => by rw [M_eq_zero 0 (j + 1) (by omega), zero_mul])]
    rcases k with _ | k <;> simp [M, N]
  | succ n ih =>
    intro L k hL
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [sum_range_succ']
    simp only [M_succ_succ, M_succ_zero, add_mul, sum_add_distrib]
    have h2 : ∑ j ∈ range L, M n (j + 2) * N (j + 1) k + M n 1 * N 0 k =
        ∑ j ∈ range (L + 1), M n (j + 1) * N j k := by
      rw [sum_range_succ']
    have h3 : ∑ j ∈ range (L + 1), M n (j + 1) * N j k + M n 0 * N 0 k =
        ∑ j ∈ range (L + 2), M n j * prevN j k := by
      rw [sum_range_succ' _ (L + 1)]
      rfl
    have h1 : ∑ j ∈ range L, M n j * N (j + 1) k = ∑ j ∈ range (L + 2), M n j * N (j + 1) k := by
      rw [sum_range_succ, sum_range_succ, M_eq_zero n L (by omega),
        M_eq_zero n (L + 1) (by omega)]
      ring
    have key : ∑ j ∈ range (L + 2), M n j * N (j + 1) k + ∑ j ∈ range (L + 2), M n j * prevN j k
        = ∑ j ∈ range (L + 2), M n j * (if k = 0 then 0 else N j (k - 1)) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl (fun j _ => ?_)
      rw [← N_shift]
      ring
    calc _ = ∑ j ∈ range (L + 2), M n j * N (j + 1) k
          + ∑ j ∈ range (L + 2), M n j * prevN j k := by
          rw [← h3, ← h2, h1]
          ring
      _ = _ := key
      _ = _ := by
        rcases k with _ | k
        · simp
        · simp only [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
          rw [ih (L + 2) k (by omega)]
          simp

/-- The inverse computed by forward substitution is `N`. -/
private theorem Minv_eq_N (n : ℕ) : ∀ k, Minv n k = N n k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k
  by_cases hk : k ≤ n
  · rw [Minv_rec n k hk, sum_congr rfl (fun j hj => by rw [ih j (mem_range.mp hj) k])]
    have h := M_mul_N n (n + 1) k (by omega)
    rw [sum_range_succ, M_diag, one_mul] at h
    by_cases hnk : k = n
    · subst hnk
      rw [if_pos rfl] at h ⊢
      linarith
    · rw [if_neg hnk]
      rw [if_neg (Ne.symm hnk)] at h
      linarith
  · rw [Minv_eq_zero n k (by omega), N_eq_zero n k (by omega)]

/-- `T(n,k) = ∑_{j ≤ n} N(n,j) N(j,k)`. -/
private def Tn (n k : ℕ) : ℤ := ∑ j ∈ range (n + 1), N n j * N j k

/-- The statement's `T` (built from `Minv`) equals `Tn`. -/
private theorem T_eq_Tn (n k : ℕ) : T n k = Tn n k := by
  unfold T Tn
  refine sum_congr rfl (fun j _ => ?_)
  rw [Minv_eq_N, Minv_eq_N]

/-- The auxiliary sum `W(m,k) = ∑_j N(m,j+1) N(j,k)`. -/
private def Wn (m k : ℕ) : ℤ := ∑ j ∈ range m, N m (j + 1) * N j k

/-- `Tn` as a sum over any range `L > n`. -/
private theorem Tn_ext (n k L : ℕ) (h : n < L) : ∑ j ∈ range L, N n j * N j k = Tn n k := by
  obtain ⟨d, rfl⟩ : ∃ d, L = n + 1 + d := ⟨L - (n + 1), by omega⟩
  rw [sum_range_add, sum_eq_zero (s := range d)
    (fun x _ => by rw [N_eq_zero n _ (by omega), zero_mul]), add_zero]
  rfl

/-- `Wn` as a sum over any range `L ≥ m`. -/
private theorem Wn_ext (m k L : ℕ) (h : m ≤ L) :
    ∑ j ∈ range L, N m (j + 1) * N j k = Wn m k := by
  obtain ⟨d, rfl⟩ : ∃ d, L = m + d := ⟨L - m, by omega⟩
  rw [sum_range_add, sum_eq_zero (s := range d)
    (fun x _ => by rw [N_eq_zero m _ (by omega), zero_mul]), add_zero]
  rfl

/-- `T(n+2,k) + T(n,k) = T(n+1,k-1) - W(n+1,k) - N(n+1,0) N(0,k)`. -/
private theorem Tn_AB (n k : ℕ) :
    Tn (n + 2) k + Tn n k =
      (if k = 0 then 0 else Tn (n + 1) (k - 1)) - Wn (n + 1) k - N (n + 1) 0 * N 0 k := by
  have h1 : Tn (n + 2) k + Tn n k = ∑ j ∈ range (n + 2), N (n + 1) j * N (j + 1) k := by
    rw [← Tn_ext n k (n + 3) (by omega), Tn, ← sum_add_distrib, sum_range_succ']
    simp only [← add_mul, N_rec, N_rec0, zero_mul, add_zero]
  have h2 : ∑ j ∈ range (n + 2), N (n + 1) j * N (j + 1) k =
      ∑ j ∈ range (n + 2), N (n + 1) j * (if k = 0 then 0 else N j (k - 1))
        - ∑ j ∈ range (n + 2), N (n + 1) j * prevN j k := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl (fun j _ => ?_)
    rw [← N_shift]
    ring
  have h3 : ∑ j ∈ range (n + 2), N (n + 1) j * prevN j k =
      Wn (n + 1) k + N (n + 1) 0 * N 0 k := by
    rw [sum_range_succ']
    rfl
  have h4 : ∑ j ∈ range (n + 2), N (n + 1) j * (if k = 0 then 0 else N j (k - 1)) =
      if k = 0 then 0 else Tn (n + 1) (k - 1) := by
    rcases k with _ | k
    · simp
    · simp only [if_neg (Nat.succ_ne_zero k)]
      rfl
  rw [h1, h2, h3, h4]
  ring

/-- `W(m+2,k) + W(m,k) = T(m+1,k)`. -/
private theorem Wn_C (m k : ℕ) : Wn (m + 2) k + Wn m k = Tn (m + 1) k := by
  rw [← Wn_ext m k (m + 2) (by omega), Wn, ← sum_add_distrib]
  simp only [← add_mul, N_rec]
  rfl

/-- The column recurrence of `T` read off the denominator `1 - xy + 3x^2 - x^3y + x^4`. -/
private theorem Tn_R (n k : ℕ) :
    Tn (n + 4) k + 3 * Tn (n + 2) k + Tn n k =
      (if k = 0 then 0 else Tn (n + 3) (k - 1) + Tn (n + 1) (k - 1)) := by
  have a1 : Tn (n + 4) k + Tn (n + 2) k =
      (if k = 0 then 0 else Tn (n + 3) (k - 1)) - Wn (n + 3) k - N (n + 3) 0 * N 0 k :=
    Tn_AB (n + 2) k
  have a2 := Tn_AB n k
  have c : Wn (n + 3) k + Wn (n + 1) k = Tn (n + 2) k := Wn_C (n + 1) k
  have r : N (n + 3) 0 + N (n + 1) 0 = 0 := N_rec0 (n + 1)
  rcases k with _ | k
  · simp only [if_true] at a1 a2 ⊢
    linear_combination a1 + a2 - c - N 0 0 * r
  · simp only [if_neg (Nat.succ_ne_zero k)] at a1 a2 ⊢
    linear_combination a1 + a2 - c - N 0 (k + 1) * r

open MvPowerSeries

/-- The coefficient of `x^(m 0) y^(m 1)` in `gf` is `T(m 0, m 1)`. -/
private theorem coeff_gf_eq (m : Fin 2 →₀ ℕ) : coeff m gf = (T (m 0) (m 1) : ℚ) := by
  show (if m 1 ≤ m 0 then (T (m 0) (m 1) : ℚ) else 0) = _
  split_ifs with h
  · rfl
  · rw [T_eq_zero _ _ (by omega)]
    simp

/-- Coefficients of `gf` times the monomial `c x^a y^b`. -/
private theorem coeff_gf_mul (m : Fin 2 →₀ ℕ) (a b : ℕ) (c : ℚ) :
    coeff m (gf * monomial (Finsupp.single 0 a + Finsupp.single 1 b) c) =
      if a ≤ m 0 ∧ b ≤ m 1 then (T (m 0 - a) (m 1 - b) : ℚ) * c else 0 := by
  rw [coeff_mul_monomial]
  have hle : (Finsupp.single 0 a + Finsupp.single 1 b ≤ m) ↔ (a ≤ m 0 ∧ b ≤ m 1) := by
    rw [Finsupp.le_def]
    simp [Fin.forall_fin_two]
  by_cases h : a ≤ m 0 ∧ b ≤ m 1
  · rw [if_pos (hle.mpr h), if_pos h, coeff_gf_eq]
    simp [Finsupp.tsub_apply]
  · rw [if_neg (mt hle.mp h), if_neg h]

/-- Coefficients of the monomial `c x^a y^b`. -/
private theorem coeff_mono (m : Fin 2 →₀ ℕ) (a b : ℕ) (c : ℚ) :
    coeff m (monomial (Finsupp.single 0 a + Finsupp.single 1 b) c) =
      if m 0 = a ∧ m 1 = b then c else 0 := by
  rw [coeff_monomial]
  congr 1
  rw [Finsupp.ext_iff]
  simp [Fin.forall_fin_two]

/-- The denominator as a sum of monomials. -/
private theorem den_eq : den = monomial (Finsupp.single 0 0 + Finsupp.single 1 0) 1
    - monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1
    + monomial (Finsupp.single 0 2 + Finsupp.single 1 0) 3
    - monomial (Finsupp.single 0 3 + Finsupp.single 1 1) 1
    + monomial (Finsupp.single 0 4 + Finsupp.single 1 0) (1 : ℚ) := by
  have h3 : (3 : MvPowerSeries (Fin 2) ℚ) = monomial 0 3 := by
    rw [monomial_zero_eq_C_apply, map_ofNat]
  simp only [den, X_pow_eq]
  simp only [X_def, h3, monomial_mul_monomial, Finsupp.single_zero, add_zero,
    zero_add, mul_one, ← monomial_zero_one]

/-- The numerator `(1-x)(1-x+x^2) = 1 - 2x + 2x^2 - x^3` as a sum of monomials. -/
private theorem num_eq : ((1 - X 0) * (1 - X 0 + X 0 ^ 2) : MvPowerSeries (Fin 2) ℚ) =
    monomial (Finsupp.single 0 0 + Finsupp.single 1 0) 1
    - monomial (Finsupp.single 0 1 + Finsupp.single 1 0) 2
    + monomial (Finsupp.single 0 2 + Finsupp.single 1 0) 2
    - monomial (Finsupp.single 0 3 + Finsupp.single 1 0) (1 : ℚ) := by
  have e : ((1 - X 0) * (1 - X 0 + X 0 ^ 2) : MvPowerSeries (Fin 2) ℚ) =
      1 - 2 * X 0 + 2 * X 0 ^ 2 - X 0 ^ 3 := by ring
  have h2 : (2 : MvPowerSeries (Fin 2) ℚ) = monomial 0 2 := by
    rw [monomial_zero_eq_C_apply, map_ofNat]
  rw [e]
  simp only [X_pow_eq]
  simp only [X_def, h2, monomial_mul_monomial, Finsupp.single_zero, add_zero,
    zero_add, mul_one, ← monomial_zero_one]

/-- The coefficient identity `[x^n y^k] (G · den) = [x^n y^k] (1-x)(1-x+x^2)`, over `ℤ`. -/
private theorem main_int (n k : ℕ) :
    T n k - (if 1 ≤ n ∧ 1 ≤ k then T (n - 1) (k - 1) else 0)
      + (if 2 ≤ n then T (n - 2) k * 3 else 0)
      - (if 3 ≤ n ∧ 1 ≤ k then T (n - 3) (k - 1) else 0)
      + (if 4 ≤ n then T (n - 4) k else 0) =
    (if n = 0 ∧ k = 0 then 1 else 0) - (if n = 1 ∧ k = 0 then 2 else 0)
      + (if n = 2 ∧ k = 0 then 2 else 0) - (if n = 3 ∧ k = 0 then 1 else 0) := by
  by_cases hn : 4 ≤ n
  · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
    have e1 : n + 4 - 1 = n + 3 := by omega
    have e2 : n + 4 - 2 = n + 2 := by omega
    have e3 : n + 4 - 3 = n + 1 := by omega
    have e4 : n + 4 - 4 = n := by omega
    have h := Tn_R n k
    simp only [e1, e2, e3, e4, T_eq_Tn]
    rcases k with _ | k
    · simp only [if_true] at h
      split_ifs <;> first | omega | linarith | simp_all
    · simp only [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel] at h
      simp only [Nat.add_sub_cancel]
      split_ifs <;> first | omega | linarith | simp_all
  · by_cases hk : k < 4
    · have hsmall : ∀ n < 4, ∀ k < 4,
          T n k - (if 1 ≤ n ∧ 1 ≤ k then T (n - 1) (k - 1) else 0)
            + (if 2 ≤ n then T (n - 2) k * 3 else 0)
            - (if 3 ≤ n ∧ 1 ≤ k then T (n - 3) (k - 1) else 0)
            + (if 4 ≤ n then T (n - 4) k else 0) =
          (if n = 0 ∧ k = 0 then 1 else 0) - (if n = 1 ∧ k = 0 then 2 else 0)
            + (if n = 2 ∧ k = 0 then 2 else 0) - (if n = 3 ∧ k = 0 then 1 else 0) := by
        decide +kernel
      exact hsmall n (by omega) k hk
    · have z1 : T n k = 0 := T_eq_zero _ _ (by omega)
      have z2 : T (n - 1) (k - 1) = 0 := T_eq_zero _ _ (by omega)
      have z3 : T (n - 2) k = 0 := T_eq_zero _ _ (by omega)
      have z4 : T (n - 3) (k - 1) = 0 := T_eq_zero _ _ (by omega)
      have z5 : T (n - 4) k = 0 := T_eq_zero _ _ (by omega)
      have hk0 : k ≠ 0 := by omega
      simp [z1, z2, z3, z4, z5, hk0]

/-- Robert Israel's conjectured g.f. for A126127 holds. -/
theorem result : statement := by
  rw [statement_iff, den_eq, num_eq]
  ext m
  simp only [mul_add, mul_sub, map_add, map_sub, coeff_gf_mul, coeff_mono]
  simp only [Nat.sub_zero, mul_one, zero_le, and_true, if_true]
  exact_mod_cast main_int (m 0) (m 1)

end Math0.Frontier.A126127

#math0_settles Math0.Frontier.A126127.result Math0.Statements.A126127.statement
