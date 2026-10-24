/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A209802
import Math0.Audit

/-!
# Positivity of the exponential Mertens function (A209802)

We prove Zumkeller's conjecture `a(n) > 0` for all `n ≥ 1`, where `a(n) = ∑_{k=1}^{n} μ⁽ᵉ⁾(k)`
and `μ⁽ᵉ⁾` is the exponential Möbius function (multiplicative, `μ⁽ᵉ⁾(p^e) = μ(e)`).

The idea: on a squarefree `k` all exponents are `1`, so `μ⁽ᵉ⁾(k) = 1`, and always
`|μ⁽ᵉ⁾(k)| ≤ 1`. A non-squarefree `k ≤ n` is divisible by `p^2` for a prime `p ≤ n`, and `p` is
`2`, `3` or an odd number `2j + 5` with `j < n`. Hence, with
`S(n, k) = [4 ∣ k] + [9 ∣ k] + ∑_{j<n} [(2j+5)^2 ∣ k]`, we get `μ⁽ᵉ⁾(k) ≥ 1 - 2 S(n, k)` for
`1 ≤ k ≤ n`. Summing over `k`,
`a(n) ≥ n - 2 (⌊n/4⌋ + ⌊n/9⌋ + ∑_{j<n} ⌊n/(2j+5)^2⌋) ≥ n - 2n (1/4 + 1/9 + 1/8) = n/36 > 0`,
using the telescoping bound `1/(2j+5)^2 ≤ 1/(4j+8) - 1/(4j+12)`, which gives
`∑_{j<N} 1/(2j+5)^2 ≤ 1/8`.
-/

namespace Math0.Frontier.A209802
open Math0.Statements.A209802 ArithmeticFunction Finset

/-- On a squarefree `k` every exponent `v_p(k)` is `1`, so `μ⁽ᵉ⁾(k) = ∏ μ(1) = 1`. -/
private theorem muE_of_squarefree {k : ℕ} (hk : Squarefree k) : muE k = 1 := by
  unfold muE
  rw [Finsupp.prod]
  refine Finset.prod_eq_one fun p hp => ?_
  have h1 : k.factorization p ≤ 1 := hk.natFactorization_le_one p
  have h2 : k.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have h3 : k.factorization p = 1 := by omega
  rw [h3, moebius_apply_one]

/-- `|μ⁽ᵉ⁾(k)| ≤ 1`, as a product of values of `μ`. -/
private theorem abs_muE_le (k : ℕ) : |muE k| ≤ 1 := by
  unfold muE
  rw [Finsupp.prod, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => abs_moebius_le_one)

/-- The indicator `[d ∣ k]`. -/
private def ind (d k : ℕ) : ℤ := if d ∣ k then 1 else 0

/-- Indicators are nonnegative. -/
private theorem ind_nonneg (d k : ℕ) : 0 ≤ ind d k := by
  unfold ind; split_ifs <;> norm_num

/-- The number of squares dividing `k` among `4`, `9`, `(2j+5)^2` (`j < n`). -/
private def S (n k : ℕ) : ℤ :=
  ind 4 k + ind 9 k + ∑ j ∈ range n, ind ((2 * j + 5) ^ 2) k

/-- `S(n, k) ≥ 0`. -/
private theorem S_nonneg (n k : ℕ) : 0 ≤ S n k := by
  unfold S
  have := ind_nonneg 4 k
  have := ind_nonneg 9 k
  have := Finset.sum_nonneg fun j (_ : j ∈ range n) => ind_nonneg ((2 * j + 5) ^ 2) k
  linarith

/-- Pointwise: `1 - 2 S(n,k) ≤ μ⁽ᵉ⁾(k)` for `1 ≤ k ≤ n`. -/
private theorem pointwise {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : 1 - 2 * S n k ≤ muE k := by
  by_cases hsq : Squarefree k
  · rw [muE_of_squarefree hsq]
    have := S_nonneg n k
    linarith
  · have hm : -1 ≤ muE k := (abs_le.mp (abs_muE_le k)).1
    suffices h : 1 ≤ S n k by linarith
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨p, hp, hpk⟩ := hsq
    have hp' : p.Prime := hp
    have hple : p ≤ k := (Nat.le_of_dvd (by omega) (dvd_trans (dvd_mul_right p p) hpk))
    have h4 := ind_nonneg 4 k
    have h9 := ind_nonneg 9 k
    have hs := Finset.sum_nonneg fun j (_ : j ∈ range n) => ind_nonneg ((2 * j + 5) ^ 2) k
    unfold S
    by_cases h2 : p = 2
    · subst h2
      have : ind 4 k = 1 := by unfold ind; rw [if_pos (by simpa using hpk)]
      linarith
    by_cases h3 : p = 3
    · subst h3
      have : ind 9 k = 1 := by unfold ind; rw [if_pos (by simpa using hpk)]
      linarith
    have hodd : Odd p := hp'.odd_of_ne_two h2
    have hp2 := hp'.two_le
    have h4' : p ≠ 4 := by rintro rfl; exact absurd hp' (by decide)
    obtain ⟨m, hm'⟩ := hodd
    set j := (p - 5) / 2 with hj
    have hjp : 2 * j + 5 = p := by omega
    have hjn : j ∈ range n := by rw [mem_range]; omega
    have hterm : ind ((2 * j + 5) ^ 2) k = 1 := by
      unfold ind; rw [if_pos (by rw [hjp, sq]; exact hpk)]
    have := Finset.single_le_sum (f := fun j => ind ((2 * j + 5) ^ 2) k)
      (fun j (_ : j ∈ range n) => ind_nonneg ((2 * j + 5) ^ 2) k) hjn
    linarith

/-- `∑_{k=1}^{n} [d ∣ k] = ⌊n/d⌋`. -/
private theorem sum_ind (n d : ℕ) : ∑ k ∈ Icc 1 n, ind d k = ((n / d : ℕ) : ℤ) := by
  unfold ind
  rw [Finset.sum_boole, ← Nat.Ioc_filter_dvd_card_eq_div n d]
  rfl

/-- Telescoping: `∑_{j<N} 1/(2j+5)^2 ≤ 1/8 - 1/(4N+8)`. -/
private theorem tele (N : ℕ) :
    ∑ j ∈ range N, (1 : ℚ) / ((2 * (j : ℚ) + 5) ^ 2) ≤ (1 : ℚ) / 8 - 1 / (4 * (N : ℚ) + 8) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ]
    have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
    have key : (1 : ℚ) / ((2 * N + 5) ^ 2) ≤ 1 / (4 * N + 8) - 1 / (4 * ((N + 1 : ℕ) : ℚ) + 8) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast at key ⊢
    linarith

/-- `∑_{j<N} n/(2j+5)^2 ≤ n/8`. -/
private theorem tail_le (n : ℕ) :
    ∑ j ∈ range n, (((n / (2 * j + 5) ^ 2 : ℕ) : ℤ) : ℚ) ≤ (n : ℚ) / 8 := by
  calc ∑ j ∈ range n, (((n / (2 * j + 5) ^ 2 : ℕ) : ℤ) : ℚ)
      ≤ ∑ j ∈ range n, (n : ℚ) * (1 / ((2 * j + 5) ^ 2)) := by
        refine sum_le_sum fun j _ => ?_
        rw [Int.cast_natCast, mul_one_div]
        have := Nat.cast_div_le (α := ℚ) (m := n) (n := (2 * j + 5) ^ 2)
        push_cast at this
        exact this
    _ = (n : ℚ) * ∑ j ∈ range n, (1 / ((2 * (j : ℚ) + 5) ^ 2)) := by rw [mul_sum]
    _ ≤ (n : ℚ) * (1 / 8) := by
        have := tele n
        have : (0 : ℚ) < 1 / (4 * n + 8) := by positivity
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        linarith
    _ = (n : ℚ) / 8 := by ring

/-- Zumkeller's conjecture (A209802): the partial sums `a(n) = ∑_{k=1}^{n} μ⁽ᵉ⁾(k)` of the
exponential Möbius function are positive for every `n ≥ 1`; the argument gives `a(n) ≥ n/36`. -/
theorem result : statement := by
  intro n hn
  have hlow : ∑ k ∈ Icc 1 n, (1 - 2 * S n k) ≤ a n := by
    unfold a
    refine sum_le_sum fun k hk => ?_
    rw [mem_Icc] at hk
    exact pointwise hk.1 hk.2
  have hsum : ∑ k ∈ Icc 1 n, (1 - 2 * S n k) = (n : ℤ) - 2 * (((n / 4 : ℕ) : ℤ) + ((n / 9 : ℕ) : ℤ)
      + ∑ j ∈ range n, ((n / (2 * j + 5) ^ 2 : ℕ) : ℤ)) := by
    rw [sum_sub_distrib, ← mul_sum]
    unfold S
    rw [sum_add_distrib, sum_add_distrib, sum_comm, sum_ind, sum_ind]
    simp only [sum_ind, sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hbound : 2 * (((n / 4 : ℕ) : ℤ) + ((n / 9 : ℕ) : ℤ)
      + ∑ j ∈ range n, ((n / (2 * j + 5) ^ 2 : ℕ) : ℤ)) < (n : ℤ) := by
    have h4 : (((n / 4 : ℕ) : ℤ) : ℚ) ≤ (n : ℚ) / 4 := by
      rw [Int.cast_natCast]; exact_mod_cast Nat.cast_div_le
    have h9 : (((n / 9 : ℕ) : ℤ) : ℚ) ≤ (n : ℚ) / 9 := by
      rw [Int.cast_natCast]; exact_mod_cast Nat.cast_div_le
    have ht := tail_le n
    have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
    have : ((2 * (((n / 4 : ℕ) : ℤ) + ((n / 9 : ℕ) : ℤ)
      + ∑ j ∈ range n, ((n / (2 * j + 5) ^ 2 : ℕ) : ℤ)) : ℤ) : ℚ) < ((n : ℤ) : ℚ) := by
      rw [Int.cast_mul, Int.cast_add, Int.cast_add, Int.cast_sum, Int.cast_natCast (n := n)]
      push_cast at h4 h9 ht ⊢
      linarith
    exact_mod_cast this
  linarith

end Math0.Frontier.A209802

#math0_settles Math0.Frontier.A209802.result Math0.Statements.A209802.statement
