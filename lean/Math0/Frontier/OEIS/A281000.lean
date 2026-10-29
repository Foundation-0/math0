/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A281000
import Math0.Audit

/-!
# Schulte's conjectures on A281000, `T(n,k) = C(2n+1,2k+1)·Cat(n-k)`

We prove all three conjectures of Werner Schulte (Jan 12 2017) as encoded in the statement file:
(1) the antidiagonal sums are the little Schröder numbers A001003(n+1); (2) (corrected reading)
`Σ_k T(n,k)(2k+1)Cat(k)·A103365(k+1) = 0^n`; (3) the inverse of `T` is
`T(n,k)·A103365(n+1-k)`.

**Inverse (3), (2).** In factorial form `T(k+p,k) = (2(k+p)+1)!/((2k+1)!·p!·(p+1)!)` and
`N(i+j+1,j+1) = (i+j+1)!(i+j)!/((j+1)!·j!·i!·(i+1)!)` (Narayana). Hence for `j ≤ p`
`T(k+p,k+j)·T(k+j,k) = F(k,p)·N(p+1,j+1)` with `F` independent of `j`, so the `(k+p,k)` entry
of `T·U` is `F(k,p)·Σ_j N(p+1,j+1)·A103365(j+1) = F(k,p)·[p = 0] = [p = 0]`, the middle sum being
the defining property of A103365 (first column of the inverse Narayana matrix, obtained from the
forward-substitution recursion). Thus `T·U = I` on every leading block, and `T⁻¹ = U`.
Conjecture (2) is the column `k = 0`, since `T(k,0) = (2k+1)·Cat(k)`.

**Antidiagonals (1).** Using `N(M+1,i+1)(i+1) = C(M,i)C(M+1,i)`,
`C(M,i)C(i,2k) = C(M,2k)C(M-2k,i-2k)` and Vandermonde one gets, for `M = 2k+p`,
`Σ_i N(M+1,i+1)·C(i+1,2k+1) = C(2k+p,2k)·C(2k+2p+1,p+1)/(2k+1) = T(k+p,k)`.
Summing over `k ≤ n/2` (with `M = n`) and exchanging sums gives
`Σ_i N(n+1,i+1)·Σ_k C(i+1,2k+1) = Σ_i N(n+1,i+1)·2^i = A001003(n+1)`.
-/

namespace Math0.Frontier.A281000
open Math0.Statements.A281000
open Finset
open scoped Nat

/-- `T` vanishes above the diagonal: `C(2n+1, 2k+1) = 0` for `k > n`. -/
private theorem T_eq_zero {n k : ℕ} (h : n < k) : T n k = 0 := by
  unfold T
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- On and below the diagonal the division in `T` is exact:
`T(k+p, k) = C(2(k+p)+1, 2k+1)·Cat(p)`. -/
private theorem T_add (k p : ℕ) :
    T (k + p) k = (2 * (k + p) + 1).choose (2 * k + 1) * catalan p := by
  unfold T
  have h1 : 2 * (k + p) - 2 * k = 2 * p := by omega
  have h2 : k + p - k = p := by omega
  have h3 : k + p + 1 - k = p + 1 := by omega
  rw [h1, h2, h3, ← Nat.centralBinom_eq_two_mul_choose, ← succ_mul_catalan_eq_centralBinom,
    Nat.mul_left_comm, Nat.mul_div_cancel_left _ (Nat.succ_pos p)]

/-- `Cat(p)·p!·(p+1)! = (2p)!`. -/
private theorem catalan_mul_fact (p : ℕ) : catalan p * p ! * (p + 1)! = (2 * p)! := by
  have h := Nat.add_choose_mul_factorial_mul_factorial p p
  rw [← two_mul, ← Nat.centralBinom_eq_two_mul_choose, ← succ_mul_catalan_eq_centralBinom]
    at h
  rw [← h, Nat.factorial_succ]
  ring

/-- Factorial form of `T`: `T(k+p, k)·(2k+1)!·p!·(p+1)! = (2(k+p)+1)!`. -/
private theorem T_mul_fact (k p : ℕ) :
    T (k + p) k * ((2 * k + 1)! * p ! * (p + 1)!) = (2 * (k + p) + 1)! := by
  rw [T_add]
  have h := Nat.add_choose_mul_factorial_mul_factorial (2 * p) (2 * k + 1)
  have e : 2 * p + (2 * k + 1) = 2 * (k + p) + 1 := by ring
  rw [e] at h
  rw [← h, ← catalan_mul_fact]
  ring

/-- Rational closed form `T(k+p, k) = (2(k+p)+1)! / ((2k+1)!·p!·(p+1)!)`. -/
private theorem T_q (k p : ℕ) :
    (T (k + p) k : ℚ) = (2 * (k + p) + 1)! / ((2 * k + 1)! * p ! * (p + 1)!) := by
  rw [eq_div_iff (by positivity)]
  exact_mod_cast T_mul_fact k p

/-- `(i+1) ∣ C(M,i)·C(M+1,i)`, so the Narayana division is exact. -/
private theorem nar_dvd (M i : ℕ) : i + 1 ∣ M.choose i * (M + 1).choose i := by
  have h1 : i + 1 ∣ (M + 1) * (M.choose i * (M + 1).choose i) := by
    have := Nat.add_one_mul_choose_eq M i
    exact ⟨(M + 1).choose (i + 1) * (M + 1).choose i, by rw [← Nat.mul_assoc, this]; ring⟩
  have h2 : i + 1 ∣ (M + 2) * (M.choose i * (M + 1).choose i) := by
    have := Nat.add_one_mul_choose_eq (M + 1) i
    exact ⟨(M + 2).choose (i + 1) * M.choose i, by
      rw [show (M + 2) * (M.choose i * (M + 1).choose i)
          = ((M + 1 + 1) * (M + 1).choose i) * M.choose i by ring, this]; ring⟩
  have h3 := Nat.dvd_sub h2 h1
  rwa [show (M + 2) * (M.choose i * (M + 1).choose i) =
      (M + 1) * (M.choose i * (M + 1).choose i) + M.choose i * (M + 1).choose i by ring,
    Nat.add_sub_cancel_left] at h3

/-- The Narayana division is exact: `N(M+1, i+1)·(i+1) = C(M,i)·C(M+1,i)`. -/
private theorem nar_mul (M i : ℕ) :
    narayana (M + 1) (i + 1) * (i + 1) = M.choose i * (M + 1).choose i := by
  unfold narayana
  simp only [Nat.add_sub_cancel]
  exact Nat.div_mul_cancel (nar_dvd M i)

/-- Factorial form of Narayana numbers:
`N(i+j+1, j+1)·(j+1)!·j!·i!·(i+1)! = (i+j+1)!·(i+j)!`. -/
private theorem nar_mul_fact (j i : ℕ) :
    narayana (i + j + 1) (j + 1) * ((j + 1)! * j ! * i ! * (i + 1)!) = (i + j + 1)! * (i + j)! := by
  have h := nar_mul (i + j) j
  have h1 := Nat.add_choose_mul_factorial_mul_factorial i j
  have h2 := Nat.add_choose_mul_factorial_mul_factorial (i + 1) j
  rw [show i + 1 + j = i + j + 1 by ring] at h2
  rw [← h1, ← h2, Nat.factorial_succ j]
  calc narayana (i + j + 1) (j + 1) * ((j + 1) * j ! * j ! * i ! * (i + 1)!)
      = (narayana (i + j + 1) (j + 1) * (j + 1)) * j ! * j ! * i ! * (i + 1)! := by ring
    _ = _ := by rw [h]; ring

/-- The list `invNarayanaCol m` has length `m`. -/
private theorem invNarayanaCol_length (m : ℕ) : (invNarayanaCol m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [invNarayanaCol, ih]

/-- Entry `j < m` of `invNarayanaCol m` is `A103365 (j+1)` (the lists are prefixes of each
other). -/
private theorem invNarayanaCol_getD (m j : ℕ) (h : j < m) :
    (invNarayanaCol m).getD j 0 = A103365 (j + 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · rw [invNarayanaCol, List.getD_append _ _ _ _ (by rw [invNarayanaCol_length]; exact h)]
      exact ih h
    · subst h; simp [A103365]

/-- A `List.range` sum is a `Finset.range` sum. -/
private theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ((List.range m).map f).sum = ∑ j ∈ range m, f j := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The forward-substitution recursion
`A103365(m+1) = [m = 0] - Σ_{j<m} N(m+1, j+1)·A103365(j+1)`. -/
private theorem A103365_succ (m : ℕ) :
    A103365 (m + 1) = (if m = 0 then 1 else 0) -
      ∑ j ∈ range m, (narayana (m + 1) (j + 1) : ℤ) * A103365 (j + 1) := by
  rw [A103365, Nat.add_sub_cancel, invNarayanaCol]
  rw [List.getD_append_right _ _ _ _ (by rw [invNarayanaCol_length]),
    invNarayanaCol_length, Nat.sub_self, list_sum_range]
  simp only [List.getD_cons_zero]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [invNarayanaCol_getD m j (mem_range.1 hj)]

/-- `A103365` is the first column of the inverse Narayana matrix:
`Σ_{j≤m} N(m+1, j+1)·A103365(j+1) = [m = 0]`. -/
private theorem nar_sum (m : ℕ) :
    ∑ j ∈ range (m + 1), (narayana (m + 1) (j + 1) : ℤ) * A103365 (j + 1) =
      if m = 0 then 1 else 0 := by
  rw [sum_range_succ]
  have h : narayana (m + 1) (m + 1) = 1 := by
    have := nar_mul m m
    simp only [Nat.choose_self, Nat.choose_succ_self_right, one_mul] at this
    exact (Nat.mul_eq_right (Nat.succ_ne_zero m)).1 this
  rw [h, A103365_succ m]
  push_cast
  ring

/-- The key factorisation: for `j ≤ p`,
`T(k+p, k+j)·T(k+j, k) = F(k,p)·N(p+1, j+1)` with
`F(k,p) = (2(k+p)+1)! / ((2k+1)!·(p+1)!·p!)` independent of `j`. -/
private theorem term_eq (k p j : ℕ) (hj : j ≤ p) :
    (T (k + p) (k + j) : ℚ) * T (k + j) k =
      (2 * (k + p) + 1)! / ((2 * k + 1)! * (p + 1)! * p !) * narayana (p + 1) (j + 1) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  have e1 : k + (j + i) = k + j + i := by ring
  have e2 : j + i = i + j := by ring
  rw [e1, T_q, T_q, e2]
  have hN : (narayana (i + j + 1) (j + 1) : ℚ) =
      (i + j + 1)! * (i + j)! / ((j + 1)! * j ! * i ! * (i + 1)!) := by
    rw [eq_div_iff (by positivity)]; exact_mod_cast nar_mul_fact j i
  rw [hN]
  field_simp

/-- The `(k+p, k)` entry of `T·U` is `[p = 0]`. -/
private theorem main (k p : ℕ) :
    ∑ l ∈ range (k + p + 1), (T (k + p) l : ℚ) * ((T l k : ℚ) * (A103365 (l + 1 - k) : ℚ)) =
      if p = 0 then 1 else 0 := by
  rw [show range (k + p + 1) = range (k + (p + 1)) from rfl, sum_range_add]
  have h0 : ∑ l ∈ range k, (T (k + p) l : ℚ) * ((T l k : ℚ) * (A103365 (l + 1 - k) : ℚ)) = 0 := by
    refine sum_eq_zero fun l hl => ?_
    rw [T_eq_zero (mem_range.1 hl)]; simp
  rw [h0, zero_add]
  have h1 : ∀ j ∈ range (p + 1), (T (k + p) (k + j) : ℚ) *
      ((T (k + j) k : ℚ) * (A103365 (k + j + 1 - k) : ℚ)) =
      (2 * (k + p) + 1)! / ((2 * k + 1)! * (p + 1)! * p !) *
        (((narayana (p + 1) (j + 1) : ℤ) * A103365 (j + 1) : ℤ) : ℚ) := by
    intro j hj
    rw [show k + j + 1 - k = j + 1 by omega, ← mul_assoc,
      term_eq k p j (Nat.lt_succ_iff.1 (mem_range.1 hj))]
    push_cast; ring
  rw [sum_congr rfl h1, ← mul_sum, ← Int.cast_sum, nar_sum]
  split_ifs with hp
  · subst hp; simp [Nat.factorial_ne_zero]
  · simp

/-- Row `n` of `T` against column `k` of `U = T(·,·)·A103365(·+1-·)`, summed over any range
longer than `n`, gives `[n = k]`. -/
private theorem main' (n k N : ℕ) (hn : n < N) :
    ∑ l ∈ range N, (T n l : ℚ) * ((T l k : ℚ) * (A103365 (l + 1 - k) : ℚ)) =
      if n = k then 1 else 0 := by
  rcases le_or_gt k n with h | h
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← sum_subset (range_subset_range.2 (show k + p + 1 ≤ N by omega)), main]
    · simp
    · intro l hl hl'
      rw [T_eq_zero (by simp at hl hl'; omega)]; simp
  · rw [if_neg (by omega)]
    refine sum_eq_zero fun l _ => ?_
    rcases le_or_gt l n with h' | h'
    · rw [T_eq_zero (show l < k by omega)]; simp
    · rw [T_eq_zero h']; simp

/-- Conjecture (3). -/
private theorem conj3_proof : conj3 := by
  intro N
  apply Matrix.inv_eq_right_inv
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun l => (T i l : ℚ) * ((T l j : ℚ) * (A103365 (l + 1 - j) : ℚ))) N, main' _ _ _ i.isLt]
  simp [Fin.ext_iff]

/-- First column: `T(k, 0) = (2k+1)·Cat(k)`. -/
private theorem T_zero (k : ℕ) : T k 0 = (2 * k + 1) * catalan k := by
  have := T_add 0 k
  simpa using this

/-- Conjecture (2) (corrected reading): it is the `k = 0` column of `T·U = I`. -/
private theorem conj2_proof : conj2 := by
  intro n
  have h := main' n 0 (n + 1) (Nat.lt_succ_self n)
  have h' : ∑ k ∈ range (n + 1),
      ((T n k : ℤ) * (2 * k + 1) * (catalan k : ℤ) * A103365 (k + 1) : ℤ) =
      if n = 0 then 1 else 0 := by
    have h'' : ((∑ k ∈ range (n + 1),
        ((T n k : ℤ) * (2 * k + 1) * (catalan k : ℤ) * A103365 (k + 1) : ℤ) : ℤ) : ℚ) =
        ((if n = 0 then 1 else 0 : ℤ) : ℚ) := by
      have e : ((if n = 0 then 1 else 0 : ℤ) : ℚ) = if n = 0 then 1 else 0 := by
        split_ifs <;> simp
      rw [e, ← h]
      push_cast
      refine sum_congr rfl fun k _ => ?_
      rw [T_zero]; push_cast
      ring
    exact_mod_cast h''
  rw [h']
  rcases n with _ | n <;> simp

/-! ### Conjecture (1) -/

/-- Grouping a sum over `range (2M)` into consecutive pairs. -/
private theorem sum_pairs (f : ℕ → ℕ) (M : ℕ) :
    ∑ k ∈ range M, (f (2 * k) + f (2 * k + 1)) = ∑ t ∈ range (2 * M), f t := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, show 2 * (M + 1) = 2 * M + 1 + 1 by ring, sum_range_succ,
      sum_range_succ]
    ring

/-- `Σ_{k<M} C(i+1, 2k+1) = 2^i` when `i < 2M` (odd-index binomial sum). -/
private theorem odd_sum (i M : ℕ) (h : i < 2 * M) :
    ∑ k ∈ range M, (i + 1).choose (2 * k + 1) = 2 ^ i := by
  simp_rw [Nat.choose_succ_succ']
  have := sum_pairs (fun t => i.choose t) M
  rw [this, ← Nat.sum_range_choose i]
  symm
  apply sum_subset (range_subset_range.2 (by omega))
  intro t ht ht'
  exact Nat.choose_eq_zero_of_lt (by simp at ht ht'; omega)

/-- By `C(M,i)·C(i,2k) = C(M,2k)·C(M-2k, i-2k)` and Vandermonde:
`Σ_i C(2k+p, i)·C(2k+p+1, i)·C(i, 2k) = C(2k+p, 2k)·C(2k+2p+1, p+1)`. -/
private theorem vandermonde_step (k p : ℕ) :
    ∑ i ∈ range (2 * k + p + 1),
      (2 * k + p).choose i * (2 * k + p + 1).choose i * i.choose (2 * k) =
      (2 * k + p).choose (2 * k) * (2 * k + 2 * p + 1).choose (p + 1) := by
  rw [show range (2 * k + p + 1) = range (2 * k + (p + 1)) from rfl, sum_range_add]
  have h0 : ∑ i ∈ range (2 * k),
      (2 * k + p).choose i * (2 * k + p + 1).choose i * i.choose (2 * k) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    rw [Nat.choose_eq_zero_of_lt (mem_range.1 hi)]; simp
  rw [h0, zero_add]
  have h1 : ∀ t ∈ range (p + 1),
      (2 * k + p).choose (2 * k + t) * (2 * k + p + 1).choose (2 * k + t) *
        (2 * k + t).choose (2 * k) =
      (2 * k + p).choose (2 * k) * (p.choose t * (2 * k + p + 1).choose (p + 1 - t)) := by
    intro t ht
    have ht' : t ≤ p := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have e1 := Nat.choose_mul (n := 2 * k + p) (k := 2 * k + t) (s := 2 * k) (by omega)
    rw [show 2 * k + p - 2 * k = p by omega, show 2 * k + t - 2 * k = t by omega] at e1
    rw [Nat.choose_symm_of_eq_add (show 2 * k + p + 1 = (2 * k + t) + (p + 1 - t) by omega)]
    calc (2 * k + p).choose (2 * k + t) * (2 * k + p + 1).choose (p + 1 - t) *
          (2 * k + t).choose (2 * k)
        = (2 * k + p).choose (2 * k + t) * (2 * k + t).choose (2 * k) *
          (2 * k + p + 1).choose (p + 1 - t) := by ring
      _ = _ := by rw [e1]; ring
  rw [sum_congr rfl h1, ← mul_sum]
  congr 1
  have hv := Nat.add_choose_eq p (2 * k + p + 1) (p + 1)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
    Nat.choose_eq_zero_of_lt (Nat.lt_succ_self p), zero_mul, add_zero,
    show p + (2 * k + p + 1) = 2 * k + 2 * p + 1 by ring] at hv
  exact hv.symm

/-- `C(2k+p, 2k)·C(2k+2p+1, p+1) = (2k+1)·T(k+p, k)` (factorial identity). -/
private theorem claimC (k p : ℕ) :
    (2 * k + p).choose (2 * k) * (2 * k + 2 * p + 1).choose (p + 1) =
      (2 * k + 1) * T (k + p) k := by
  have hX : 0 < (2 * k)! * p ! * (p + 1)! := by positivity
  apply Nat.eq_of_mul_eq_mul_right hX
  have h1 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ 2 * k + p by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show p + 1 ≤ 2 * k + 2 * p + 1 by omega)
  rw [show 2 * k + p - 2 * k = p by omega] at h1
  rw [show 2 * k + 2 * p + 1 - (p + 1) = 2 * k + p by omega] at h2
  have h3 := T_mul_fact k p
  rw [Nat.factorial_succ (2 * k), show 2 * (k + p) + 1 = 2 * k + 2 * p + 1 by ring] at h3
  calc (2 * k + p).choose (2 * k) * (2 * k + 2 * p + 1).choose (p + 1) *
        ((2 * k)! * p ! * (p + 1)!)
      = (2 * k + 2 * p + 1).choose (p + 1) * (p + 1)! *
        ((2 * k + p).choose (2 * k) * (2 * k)! * p !) := by ring
    _ = (2 * k + 2 * p + 1)! := by rw [h1, h2]
    _ = _ := by rw [← h3]; ring

/-- `T(k+p, k) = Σ_{i} N(2k+p+1, i+1)·C(i+1, 2k+1)`. -/
private theorem claimA (k p : ℕ) :
    T (k + p) k = ∑ i ∈ range (2 * k + p + 1),
      narayana (2 * k + p + 1) (i + 1) * (i + 1).choose (2 * k + 1) := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 * k + 1 by omega)
  rw [← claimC, mul_sum, ← vandermonde_step]
  refine sum_congr rfl fun i _ => ?_
  symm
  apply Nat.eq_of_mul_eq_mul_right (show 0 < i + 1 by omega)
  have h1 := nar_mul (2 * k + p) i
  have h2 := Nat.add_one_mul_choose_eq i (2 * k)
  calc (2 * k + 1) * (narayana (2 * k + p + 1) (i + 1) * (i + 1).choose (2 * k + 1)) * (i + 1)
      = (narayana (2 * k + p + 1) (i + 1) * (i + 1)) *
        ((i + 1).choose (2 * k + 1) * (2 * k + 1)) := by ring
    _ = _ := by rw [h1, ← h2]; ring

/-- Conjecture (1). -/
private theorem conj1_proof : conj1 := by
  intro n
  have hL : ∀ k ∈ range (n / 2 + 1), T (n - k) k =
      ∑ i ∈ range (n + 1), narayana (n + 1) (i + 1) * (i + 1).choose (2 * k + 1) := by
    intro k hk
    have hk' : 2 * k ≤ n := by simp at hk; omega
    have := claimA k (n - 2 * k)
    rw [show k + (n - 2 * k) = n - k by omega, show 2 * k + (n - 2 * k) = n by omega] at this
    exact this
  rw [sum_congr rfl hL, sum_comm]
  simp_rw [← mul_sum]
  rw [A001003, if_neg (Nat.succ_ne_zero n), ← Finset.Ico_add_one_right_eq_Icc,
    sum_Ico_eq_sum_range]
  rw [show n + 1 + 1 - 1 = n + 1 by omega]
  refine sum_congr rfl fun i hi => ?_
  rw [odd_sum i _ (by simp at hi; omega), add_comm 1 i, Nat.add_sub_cancel, mul_comm]

/-- Werner Schulte's conjectures (1), (2) (corrected reading) and (3) on A281000 all hold. -/
theorem result : statement := ⟨conj1_proof, conj2_proof, conj3_proof⟩

end Math0.Frontier.A281000

#math0_settles Math0.Frontier.A281000.result Math0.Statements.A281000.statement
