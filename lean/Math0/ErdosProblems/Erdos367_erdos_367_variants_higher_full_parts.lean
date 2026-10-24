/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«367»
import Math0.Audit

/-!
# Erdős Problem 367: products of `r`-full parts beat `n^(1+ε)` infinitely often

For `r ≥ 3`, `k ≥ 2` let `B_r(m)` be the `r`-full part of `m` (Erdős–Graham; erdosproblems.com/367).
We prove the upstream statement exactly as formalized: for every such `r, k` there is an
`ε = ε(r, k) > 0` (we take `ε = 1/(2r)`) with
`limsup_{n → ∞} (∏_{n ≤ m < n+k} B_r(m)) / n^(1+ε) = ∞` in `EReal`.
Take `t = 2^(rj)`, `A = t + 1` and `n = A^r - 1`. Then `B_r(n+1) = B_r(A^r) = A^r` since every
prime exponent of `A^r` is a multiple of `r`, and `t = A - 1 ∣ A^r - 1 = n`, so the `2`-part of
`n` contributes `B_r(n) ≥ t`. Hence the product is `≥ t·A^r`, while `n^(1+ε) ≤ A^r·√A`, so the
ratio is `≥ t/√(t+1) → ∞` as `j → ∞`.
-/

open Filter Erdos367

namespace Math0.Erdos367

/-- The `r`-full part `B r m` is always positive (an empty product is `1`). -/
theorem B_pos (r m : ℕ) : 0 < B r m := by
  unfold B
  apply Finset.prod_pos
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).1
  have hp : i.Prime := Nat.prime_of_mem_primeFactors (by simpa using hi')
  exact pow_pos hp.pos _

/-- An `r`-th power is its own `r`-full part: `B_r(A^r) = A^r` for `A ≠ 0`. -/
theorem B_pow_self (r A : ℕ) (hA : A ≠ 0) : B r (A ^ r) = A ^ r := by
  unfold B
  rw [Finset.filter_true_of_mem]
  · exact Nat.prod_factorization_pow_eq_self (pow_ne_zero _ hA)
  · intro i hi
    rw [Finsupp.mem_support_iff] at hi
    rw [Nat.factorization_pow] at hi ⊢
    simp only [Finsupp.smul_apply, smul_eq_mul] at hi ⊢
    have : A.factorization i ≠ 0 := by
      intro h; rw [h] at hi; simp at hi
    calc r = r * 1 := by ring
      _ ≤ r * A.factorization i := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr this)

/-- If `2^e ∣ n ≠ 0` with `1 ≤ r ≤ e`, then the `2`-part of `n` is `r`-full, so `2^e ≤ B_r(n)`. -/
theorem two_pow_le_B (r n e : ℕ) (hn : n ≠ 0) (hr1 : 1 ≤ r) (hr : r ≤ e) (h : 2 ^ e ∣ n) :
    2 ^ e ≤ B r n := by
  have he : e ≤ n.factorization 2 := (Nat.prime_two.pow_dvd_iff_le_factorization hn).mp h
  calc 2 ^ e ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by norm_num) he
    _ ≤ B r n := by
      unfold B
      apply Finset.single_le_prod' (f := fun i => i ^ n.factorization i)
      · intro i hi
        have hi' := (Finset.mem_filter.mp hi).1
        have hp : i.Prime := Nat.prime_of_mem_primeFactors (by simpa using hi')
        exact Nat.one_le_pow _ _ hp.pos
      · rw [Finset.mem_filter, Finsupp.mem_support_iff]
        omega

/-- For `k ≥ 2` the product over `[n, n+k)` is at least `B_r(n)·B_r(n+1)`. -/
theorem pair_le_prod (r n k : ℕ) (hk : 2 ≤ k) :
    B r n * B r (n + 1) ≤ ∏ m ∈ Finset.Ico n (n + k), B r m := by
  have hsub : ({n, n + 1} : Finset ℕ) ⊆ Finset.Ico n (n + k) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Ico]
    omega
  have := Finset.prod_le_prod_of_subset_of_one_le' hsub (f := fun m => B r m)
    (fun i _ _ => B_pos r i)
  rw [Finset.prod_pair (by omega)] at this
  exact this

/-- For all `r ≥ 3`, `k ≥ 2` there is `ε > 0` (namely `1/(2r)`) such that
`limsup (∏_{n ≤ m < n+k} B_r(m)) / n^(1+ε) = ⊤`. -/
theorem higher_full_parts : type_of% @Erdos367.erdos_367.variants.higher_full_parts := by
  intro r k hr hk
  refine ⟨1 / (2 * r), by positivity, ?_⟩
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (lt_add_one y)) ?_
  apply le_limsup_of_frequently_le'
  rw [frequently_atTop]
  intro a
  set M : ℝ := y + 1 with hM
  set j : ℕ := a + ⌈(M + 1) ^ 2⌉₊ + 1 with hj
  set t : ℕ := 2 ^ (r * j) with ht
  set A : ℕ := t + 1 with hA
  set n : ℕ := A ^ r - 1 with hn
  have hr0 : r ≠ 0 := by omega
  have htj : j ≤ t := by
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 2 ^ j ≤ 2 ^ (r * j) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  have hAr : A ≤ A ^ r := Nat.le_self_pow hr0 A
  have hn1 : n + 1 = A ^ r := by omega
  have htn : t ≤ n := by omega
  have hn0 : n ≠ 0 := by
    have : 1 ≤ j := by omega
    omega
  have hdvd : 2 ^ (r * j) ∣ n := by
    have := Nat.sub_dvd_pow_sub_pow A 1 r
    simpa [hA, ht] using this
  have hBn : t ≤ B r n := two_pow_le_B r n (r * j) hn0 (by omega) (by nlinarith) hdvd
  have hBn1 : B r (n + 1) = A ^ r := by rw [hn1]; exact B_pow_self r A (by omega)
  have hP : t * A ^ r ≤ ∏ m ∈ Finset.Ico n (n + k), B r m := by
    calc t * A ^ r ≤ B r n * B r (n + 1) := by rw [hBn1]; exact Nat.mul_le_mul_right _ hBn
      _ ≤ _ := pair_le_prod r n k hk
  refine ⟨n, by omega, ?_⟩
  rw [EReal.coe_le_coe_iff]
  have hPR : (t:ℝ) * (A:ℝ) ^ r ≤ ((∏ m ∈ Finset.Ico n (n + k), B r m : ℕ) : ℝ) := by
    exact_mod_cast hP
  have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnA : (n:ℝ) ≤ (A:ℝ) ^ r := by exact_mod_cast (by omega : n ≤ A ^ r)
  have hApos : (0:ℝ) < A := by positivity
  have hpow : ((A:ℝ) ^ r) ^ (1 + 1 / (2 * (r:ℝ))) = (A:ℝ) ^ r * √(A:ℝ) := by
    rw [Real.rpow_add (by positivity), Real.rpow_one, ← Real.rpow_natCast_mul hApos.le,
      Real.sqrt_eq_rpow]
    congr 2
    field_simp
  have h1 : (n:ℝ) ^ (1 + 1 / (2 * (r:ℝ))) ≤ (A:ℝ) ^ r * √(A:ℝ) := by
    rw [← hpow]; exact Real.rpow_le_rpow hnR.le hnA (by positivity)
  have hsq : (√(A:ℝ)) ^ 2 = A := Real.sq_sqrt hApos.le
  have hceil : (M + 1) ^ 2 ≤ (t:ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈(M + 1) ^ 2⌉₊ ≤ t))
  have hA' : (A:ℝ) = t + 1 := by rw [hA]; push_cast; ring
  have hrp : (0:ℝ) < (n:ℝ) ^ (1 + 1 / (2 * (r:ℝ))) := Real.rpow_pos_of_pos hnR _
  rw [le_div_iff₀ hrp]
  rcases le_or_gt M 0 with hM0 | hM0
  · have : (0:ℝ) ≤ ((∏ m ∈ Finset.Ico n (n + k), B r m : ℕ) : ℝ) := by positivity
    nlinarith
  · have hs : M + 1 ≤ √(A:ℝ) := by
      rw [Real.le_sqrt (by linarith) hApos.le]; linarith
    have hst : M * √(A:ℝ) ≤ t := by nlinarith
    calc M * (n:ℝ) ^ (1 + 1 / (2 * (r:ℝ))) ≤ M * ((A:ℝ) ^ r * √(A:ℝ)) := by gcongr
      _ = (M * √(A:ℝ)) * (A:ℝ) ^ r := by ring
      _ ≤ t * (A:ℝ) ^ r := by gcongr
      _ ≤ _ := hPR

end Math0.Erdos367

#math0_proves Math0.Erdos367.higher_full_parts Erdos367.erdos_367.variants.higher_full_parts
