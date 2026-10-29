/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A211343
import Math0.Audit

/-!
# A211343: positive entries are smallest parts of consecutive-part partitions

Both conjectures of Omar E. Pol on A211343 hold. Writing `S k = 0 + 1 + ⋯ + (k-1)`, column `k`
starts in row `k(k+1)/2 = S k + k` and has period `k`, so for `k ≥ 1` the entry `T(n,k)` is
positive exactly when `n = k * m + S k` for some `m ≥ 1`, and then `T(n,k) = m`. Since
`m + (m+1) + ⋯ + (m+k-1) = k * m + S k`, this says that `T(n,k) > 0` iff `n` is a sum of `k`
consecutive positive integers, the smallest of which is `T(n,k)`. Conjecture 1 follows (the
consecutive partition with `k` parts is determined by its sum), and Conjecture 2 follows from
`A109814_isGreatest`, since the set of columns of row `n` with positive entries is exactly
`{k | IsConsecSum n k}`.
-/

namespace Math0.Frontier.A211343
open Math0.Statements.A211343
open Finset

/-- `k(k+1)/2 = (0 + 1 + ⋯ + (k-1)) + k`. -/
private lemma tri_eq (k : ℕ) : k * (k + 1) / 2 = (∑ i ∈ range k, i) + k := by
  have h := Finset.sum_range_id (k + 1)
  rw [Finset.sum_range_succ] at h
  rw [h, Nat.add_sub_cancel, Nat.mul_comm]

/-- `m + (m+1) + ⋯ + (m+k-1) = k * m + (0 + 1 + ⋯ + (k-1))`. -/
private lemma consec_sum (m k : ℕ) :
    ∑ i ∈ range k, (m + i) = k * m + ∑ i ∈ range k, i := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The multiset sum of `m, m+1, …, m+k-1` is `k * m + (0 + 1 + ⋯ + (k-1))`. -/
private lemma multiset_consec_sum (m k : ℕ) :
    ((Multiset.range k).map (fun i => m + i)).sum = k * m + ∑ i ∈ range k, i := by
  rw [← consec_sum]
  rfl

/-- A positive entry `T(n,k)` satisfies `n = k * T(n,k) + (0 + 1 + ⋯ + (k-1))`. -/
private lemma eq_of_T_pos {n k : ℕ} (h : InRow n k) (hT : 0 < T n k) :
    n = k * T n k + ∑ i ∈ range k, i := by
  have hk := h.1
  have hle := h.2
  unfold T at hT ⊢
  rw [if_pos h] at hT ⊢
  unfold column at hT ⊢
  split_ifs at hT ⊢ with hd
  · rw [tri_eq] at hle hd ⊢
    have hdiv : k ∣ n - ((∑ i ∈ range k, i) + k) := Nat.dvd_of_mod_eq_zero hd
    have := Nat.mul_div_cancel' hdiv
    rw [Nat.mul_add, this]
    omega
  · omega

/-- Conversely, if `n = k * m + (0 + 1 + ⋯ + (k-1))` with `k, m ≥ 1`, then `(n, k)` is in the
triangle and `T(n,k) = m`. -/
private lemma T_of_eq {n k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hn : n = k * m + ∑ i ∈ range k, i) : InRow n k ∧ T n k = m := by
  have hrow : InRow n k := by
    refine ⟨hk, ?_⟩
    rw [tri_eq, hn]
    have : k ≤ k * m := Nat.le_mul_of_pos_right k hm
    omega
  refine ⟨hrow, ?_⟩
  unfold T
  rw [if_pos hrow]
  unfold column
  have hj : n - k * (k + 1) / 2 = k * (m - 1) := by
    rw [tri_eq, hn, Nat.mul_sub, Nat.mul_one]
    have : k ≤ k * m := Nat.le_mul_of_pos_right k hm
    omega
  rw [hj, Nat.mul_mod_right, if_pos rfl, Nat.mul_div_cancel_left _ (by omega)]
  omega

/-- For `n ≥ 1`, the columns of row `n` with a positive entry are exactly the `k` such that `n`
is a sum of `k` consecutive positive integers. -/
private lemma inRow_T_pos_iff {n k : ℕ} (hn : 1 ≤ n) :
    (InRow n k ∧ 0 < T n k) ↔ IsConsecSum n k := by
  constructor
  · rintro ⟨h, hT⟩
    exact ⟨T n k, hT, by rw [consec_sum]; exact (eq_of_T_pos h hT).symm⟩
  · rintro ⟨m, hm, hs⟩
    rw [consec_sum] at hs
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hs; omega
      · exact h
    obtain ⟨hrow, hT⟩ := T_of_eq hk hm hs.symm
    exact ⟨hrow, by omega⟩

/-- Both conjectures hold: positive entries `T(n,k)` are the smallest parts of the (unique)
partition of `n` into `k` consecutive parts, and the last positive entry of row `n` is in
column `A109814(n)`. -/
theorem result : statement := by
  refine ⟨?_, ?_⟩
  · intro n k _ h hT
    have hk : 1 ≤ k := h.1
    have hn := eq_of_T_pos h hT
    refine ⟨?_, ?_⟩
    · refine ⟨⟨(Multiset.range k).map (fun i => T n k + i), ?_, ?_⟩, T n k, rfl⟩
      · intro i hi
        obtain ⟨j, _, rfl⟩ := Multiset.mem_map.1 hi
        omega
      · rw [multiset_consec_sum]
        exact hn.symm
    · rintro p ⟨m', hp⟩
      have hsum := p.parts_sum
      rw [hp, multiset_consec_sum] at hsum
      have hmm : k * m' = k * T n k := by omega
      have hm' : m' = T n k := Nat.eq_of_mul_eq_mul_left (by omega) hmm
      subst hm'
      refine ⟨?_, ?_⟩
      · show T n k ∈ p.parts
        rw [hp]
        exact Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), by simp⟩
      · intro x hx
        have hx' : x ∈ p.parts := hx
        rw [hp] at hx'
        obtain ⟨j, _, rfl⟩ := Multiset.mem_map.1 hx'
        omega
  · intro n hn
    have hset : {k | InRow n k ∧ 0 < T n k} = {k | IsConsecSum n k} := by
      ext k
      exact inRow_T_pos_iff hn
    rw [hset]
    exact A109814_isGreatest hn

end Math0.Frontier.A211343

#math0_settles Math0.Frontier.A211343.result Math0.Statements.A211343.statement
