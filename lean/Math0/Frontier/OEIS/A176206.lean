/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A176206
import Math0.Audit

/-!
# Divisors of the terms of row `n` of A176206 are the parts of the partitions of `n`

We prove Omar E. Pol's conjecture (A176206): for every `n ≥ 1`, the multiset of all divisors
of all terms of row `n` equals the multiset of all parts of all partitions of `n`.

Compare multiplicities of a fixed `d`. Write `c d t ∈ {0, 1}` for the multiplicity of `d` among
the divisors of `t`. Since row `n` holds `n - k` repeated `p k` times (`k < n`), the left side
has `H d n = ∑_{k<n} p k · c d (n - k)` copies of `d`. The right side has
`F d n = ∑_{π ⊢ n} (number of parts of π equal to d)` copies.

* `d = 0`: both are `0`, because `0` is not a divisor of a positive number and parts are
  positive.
* `d ≥ 1`, `n < d`: both are `0`, because parts and row terms are in `[1, n]`.
* `d ≥ 1`, `d ≤ n`: removing one part `d` is a bijection from the partitions of `n` that contain
  `d` onto the partitions of `n - d` (Mathlib's `partitionWithPartEquiv`). It lowers the count
  of `d` by exactly one, so `F d n = F d (n - d) + p (n - d)`. On the left, split
  `k < n` into `k < n - d` (where `d ∣ n - k ↔ d ∣ (n - d) - k`) and `n - d ≤ k < n`
  (where `1 ≤ n - k ≤ d`, so `d ∣ n - k` only for `k = n - d`). This gives
  `H d n = H d (n - d) + p (n - d)`.

Strong induction on `n` gives `F d n = H d n` for every `d`, and `Multiset.ext'` concludes.
-/

namespace Math0.Frontier.A176206
open Math0.Statements.A176206

/-- The multiplicity of `d` among the divisors of `t`. It is `0` or `1`. -/
private def c (d t : ℕ) : ℕ := t.divisors.val.count d

/-- `d` occurs once among the divisors of `t` if `d ∣ t` and `t ≠ 0`, and never otherwise. -/
private lemma c_eq (d t : ℕ) : c d t = if d ∣ t ∧ t ≠ 0 then 1 else 0 := by
  unfold c
  by_cases h : d ∣ t ∧ t ≠ 0
  · rw [if_pos h]
    exact Multiset.count_eq_one_of_mem t.divisors.nodup (Nat.mem_divisors.2 h)
  · rw [if_neg h]
    exact Multiset.count_eq_zero.2 fun h' => h (Nat.mem_divisors.1 h')

/-- The total number of parts equal to `d` over all partitions of `n` (the right side). -/
private def F (d n : ℕ) : ℕ := ∑ π : n.Partition, π.parts.count d

/-- The number of copies of `d` among the divisors of the terms of row `n` (the left side). -/
private def H (d n : ℕ) : ℕ := ∑ k ∈ Finset.range n, p k * c d (n - k)

/-- No partition of `n < d` has a part equal to `d`. -/
private lemma F_lt {d n : ℕ} (h : n < d) : F d n = 0 := by
  refine Finset.sum_eq_zero fun π _ => Multiset.count_eq_zero.2 fun hd => ?_
  have := part_le π hd
  omega

/-- No term `n - k ∈ [1, n]` of row `n < d` is divisible by `d`. -/
private lemma H_lt {d n : ℕ} (h : n < d) : H d n = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [c_eq, if_neg]
  · simp
  · rintro ⟨hdv, hne⟩
    have := Nat.le_of_dvd (by omega) hdv
    omega

/-- Removing one part `d` gives the recursion `F d n = F d (n - d) + p (n - d)`. -/
private lemma F_ge {d n : ℕ} (hd : 1 ≤ d) (h : d ≤ n) : F d n = F d (n - d) + p (n - d) := by
  rw [F, ← Finset.sum_filter_of_ne (p := fun π : n.Partition => d ∈ π.parts)
    (fun π _ hπ => Multiset.count_ne_zero.1 hπ)]
  rw [Finset.sum_subtype (Finset.univ.filter fun π : n.Partition => d ∈ π.parts)
    (p := fun π : n.Partition => d ∈ π.parts) (by simp)]
  rw [← Fintype.sum_equiv (Nat.Partition.partitionWithPartEquiv hd h).symm
    (fun σ : (n - d).Partition => σ.parts.count d + 1) _ (fun σ => by
      simp [Nat.Partition.partitionWithPartEquiv_symm_apply_parts])]
  rw [Finset.sum_add_distrib, F, p]
  simp

/-- The left side satisfies the same recursion, `H d n = H d (n - d) + p (n - d)`. -/
private lemma H_ge {d n : ℕ} (hd : 1 ≤ d) (h : d ≤ n) : H d n = H d (n - d) + p (n - d) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
  rw [Nat.add_sub_cancel, H, Finset.sum_range_add, H]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [c_eq, c_eq]
    congr 2
    apply propext
    have : m + d - k = (m - k) + d := by omega
    rw [this, Nat.dvd_add_self_right]
    omega
  · rw [Finset.sum_eq_single 0]
    · rw [c_eq, if_pos]
      · simp
      · constructor
        · simp
        · omega
    · intro x hx hx0
      rw [Finset.mem_range] at hx
      rw [c_eq, if_neg]
      · simp
      · rintro ⟨hdv, hne⟩
        have := Nat.le_of_dvd (by omega) hdv
        omega
    · simp; omega

/-- Parts are positive, so no part equals `0`. -/
private lemma F_zero (n : ℕ) : F 0 n = 0 :=
  Finset.sum_eq_zero fun π _ => Multiset.count_eq_zero.2 fun h => lt_irrefl 0 (π.parts_pos h)

/-- `0` is never a divisor of a positive number. -/
private lemma H_zero (n : ℕ) : H 0 n = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [c_eq, if_neg]
  · simp
  · rintro ⟨h0, hne⟩
    exact hne (Nat.eq_zero_of_zero_dvd h0)

/-- The two counts agree, by strong induction on `n`. -/
private lemma F_eq_H (d n : ℕ) : F d n = H d n := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [F_zero, H_zero]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n d with h | h
    · rw [F_lt h, H_lt h]
    · rw [F_ge hd h, H_ge hd h, ih _ (by omega)]

/-- Summing a function over a `flatMap`. -/
private lemma list_sum_flatMap (L : List ℕ) (g : ℕ → List ℕ) (f : ℕ → ℕ) :
    ((L.flatMap g).map f).sum = (L.map fun k => ((g k).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- A sum over `List.range n` is a sum over `Finset.range n`. -/
private lemma list_sum_range (h : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map h).sum = ∑ k ∈ Finset.range n, h k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- The multiplicity of `d` on the left side of the statement is `H d n`. -/
private lemma lhs_count (d n : ℕ) :
    ((row n : Multiset ℕ).map fun b => b.divisors.val.count d).sum = H d n := by
  show ((row n).map (c d)).sum = H d n
  rw [row, rowOf, list_sum_flatMap, H, ← list_sum_range]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  rw [List.map_replicate, List.sum_replicate, smul_eq_mul]

/-- Pol's conjecture (A176206) holds: for every `n ≥ 1`, the divisors of the terms of row `n`
are, as a multiset, the parts of all partitions of `n`. -/
theorem result : statement := by
  intro n _
  refine Multiset.ext' fun d => ?_
  rw [Multiset.count_bind, Multiset.count_bind, lhs_count, ← F_eq_H]
  rfl

end Math0.Frontier.A176206

#math0_settles Math0.Frontier.A176206.result Math0.Statements.A176206.statement
