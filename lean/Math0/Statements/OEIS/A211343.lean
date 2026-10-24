/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A211343: smallest parts of partitions into consecutive parts

Source: https://oeis.org/A211343, Omar E. Pol, Apr 30 2017 (COMMENTS section). Verbatim:
> Conjecture 1: T(n,k) is the smallest part of the partition of n into k consecutive parts, if
> T(n,k) > 0.
> Conjecture 2: the last positive integer in the row n is in the column A109814(n).

The entry (Omar E. Pol, Feb 05 2013; offset `1`, keyword `tabf`) is "Triangle read by rows:
T(n,k), n >= 1, k >= 1, in which column k lists the positive integers interleaved with k-1 zeros,
and the first element of column k is in row k(k+1)/2." Row `n` has length A003056(n), the
largest `k` with `k(k+1)/2 ≤ n`.

A109814 (David W. Wilson) is "a(n) is the largest k such that n can be written as sum of k
consecutive positive integers." (offset `1`).

## Encoding

* *Columns.* `column k j` is the `j`-th entry (`j = 0, 1, 2, …`) of column `k` counted from its
  first row: the positive integers interleaved with `k - 1` zeros, i.e. `1, 0^(k-1), 2, 0^(k-1),
  3, …`, so `column k j = j / k + 1` if `k ∣ j` and `0` otherwise.
* *The triangle.* Column `k ≥ 1` begins in row `k(k+1)/2`, so row `n` contains exactly the
  columns `k` with `1 ≤ k` and `k(k+1)/2 ≤ n` (`InRow n k`), and
  `T n k = column k (n - k(k+1)/2)` for those. Outside the triangle `T n k = 0` (a junk value;
  the statement never uses it). `row n` lists `T(n,1), …, T(n, A003056(n))` (all columns of row
  `n` are `≤ n`, `le_of_inRow`), and `a` is the triangle read by rows with offset `1`
  (`a i` is the `i`-th entry of the concatenation of rows `1, 2, …`; `a 0 = 0` is junk).
  `a_data` checks all 94 listed terms (rows `1..24`) in the kernel.
* *Partitions into consecutive parts.* A partition of `n` is Mathlib's `Nat.Partition n` (a
  multiset of positive integers summing to `n`). It is a partition into `k` consecutive parts
  (`HasConsecutiveParts k p`) if its multiset of parts is `{m, m+1, …, m+k-1}` for some `m`.
  "The partition" is read as: such a partition exists, and every such partition has smallest
  part `T(n,k)` (the partition is in fact unique, being determined by `k` and `n`); the
  smallest part of `p` is expressed as `IsLeast {x | x ∈ p.parts}`.
* *A109814.* `IsConsecSum n k` says that `n = m + (m+1) + … + (m+k-1)` for some `m ≥ 1`.
  `A109814 n` is computed as `Nat.findGreatest` of this property with the search for `k` and `m`
  bounded by `n`; `A109814_isGreatest` proves that for `n ≥ 1` it is the largest `k` with
  `IsConsecSum n k` (the unbounded OEIS definition), and `A109814_data` checks the first 40
  listed terms in the kernel.
* *Conjecture 1* (first conjunct of `statement`): for all `n ≥ 1` and all columns `k` of row `n`
  (`1 ≤ k`, `k(k+1)/2 ≤ n`) with `T(n,k) > 0`, there is a partition of `n` into `k` consecutive
  parts, and `T(n,k)` is the smallest part of every such partition. Only the direction stated
  ("if T(n,k) > 0") is claimed.
* *Conjecture 2* (second conjunct): for all `n ≥ 1`, the column of the last positive entry of
  row `n` is `A109814(n)`, i.e. `A109814 n` is the greatest `k` among the columns of row `n`
  with `T(n,k) > 0` (so column `A109814 n` belongs to row `n`, its entry is positive, and every
  later entry of row `n` is `0`).
-/

namespace Math0.Statements.A211343

open Finset

/-- Column `k` read from its first row: the positive integers interleaved with `k - 1` zeros,
`1, 0, …, 0, 2, 0, …, 0, 3, …`. -/
def column (k j : ℕ) : ℕ := if j % k = 0 then j / k + 1 else 0

/-- Row `n` of the triangle has an entry in column `k` iff `k ≥ 1` and column `k` has started,
i.e. its first row `k(k+1)/2` is `≤ n`. -/
def InRow (n k : ℕ) : Prop := 1 ≤ k ∧ k * (k + 1) / 2 ≤ n

instance (n k : ℕ) : Decidable (InRow n k) := by unfold InRow; infer_instance

/-- The triangle `T(n,k)`: column `k` lists the positive integers interleaved with `k - 1`
zeros and starts in row `k(k+1)/2` (junk value `0` outside the triangle). -/
def T (n k : ℕ) : ℕ := if InRow n k then column k (n - k * (k + 1) / 2) else 0

/-- Every column of row `n` has index at most `n`. -/
theorem le_of_inRow {n k : ℕ} (h : InRow n k) : k ≤ n := by
  obtain ⟨h1, h2⟩ := h
  have : k ≤ k * (k + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith
  omega

/-- Row `n` of the triangle: `T(n,1), …, T(n, A003056(n))`. -/
def row (n : ℕ) : List ℕ := ((List.range (n + 1)).filter (fun k => decide (InRow n k))).map (T n)

/-- A211343: the triangle read by rows, offset `1` (`a 0 = 0` is junk). -/
def a (i : ℕ) : ℕ := ((List.range i).flatMap (fun j => row (j + 1))).getD (i - 1) 0

/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all 94 listed
terms, i.e. rows `1` to `24`. -/
theorem a_data : (List.range 94).map (fun i => a (i + 1)) =
    [1, 2, 3, 1, 4, 0, 5, 2, 6, 0, 1, 7, 3, 0, 8, 0, 0, 9, 4, 2, 10, 0, 0, 1, 11, 5, 0, 0, 12, 0,
      3, 0, 13, 6, 0, 0, 14, 0, 0, 2, 15, 7, 4, 0, 1, 16, 0, 0, 0, 0, 17, 8, 0, 0, 0, 18, 0, 5, 3,
      0, 19, 9, 0, 0, 0, 20, 0, 0, 0, 2, 21, 10, 6, 0, 0, 1, 22, 0, 0, 4, 0, 0, 23, 11, 0, 0, 0,
      0, 24, 0, 7, 0, 0, 0] := by
  decide +kernel

/-- The same data, row by row (rows `1` to `24`), matching the example in the entry. -/
theorem row_data : (List.range 24).map (fun n => row (n + 1)) =
    [[1], [2], [3, 1], [4, 0], [5, 2], [6, 0, 1], [7, 3, 0], [8, 0, 0], [9, 4, 2], [10, 0, 0, 1],
      [11, 5, 0, 0], [12, 0, 3, 0], [13, 6, 0, 0], [14, 0, 0, 2], [15, 7, 4, 0, 1],
      [16, 0, 0, 0, 0], [17, 8, 0, 0, 0], [18, 0, 5, 3, 0], [19, 9, 0, 0, 0], [20, 0, 0, 0, 2],
      [21, 10, 6, 0, 0, 1], [22, 0, 0, 4, 0, 0], [23, 11, 0, 0, 0, 0], [24, 0, 7, 0, 0, 0]] := by
  decide +kernel

/-- A partition `p` of `n` is a partition into `k` consecutive parts: its parts are
`m, m+1, …, m+k-1` for some `m`. -/
def HasConsecutiveParts {n : ℕ} (k : ℕ) (p : n.Partition) : Prop :=
  ∃ m, p.parts = (Multiset.range k).map (fun i => m + i)

/-- `n` can be written as the sum of `k` consecutive positive integers
`m + (m+1) + … + (m+k-1)`, `m ≥ 1`. -/
def IsConsecSum (n k : ℕ) : Prop := ∃ m, 0 < m ∧ ∑ i ∈ range k, (m + i) = n

/-- `IsConsecSum n k` with the start `m` searched in `[1, n]` (decidable). -/
def IsConsecSumBdd (n k : ℕ) : Prop := ∃ m ∈ Finset.Icc 1 n, ∑ i ∈ Finset.range k, (m + i) = n

instance (n : ℕ) : DecidablePred (IsConsecSumBdd n) := fun k => by
  unfold IsConsecSumBdd; infer_instance

/-- A109814: the largest `k` such that `n` can be written as the sum of `k` consecutive positive
integers (computed with `k ≤ n` and `m ≤ n`; see `A109814_isGreatest`). -/
def A109814 (n : ℕ) : ℕ := Nat.findGreatest (IsConsecSumBdd n) n

/-- For `n ≥ 1`, `A109814 n` is the largest `k` such that `n` is the sum of `k` consecutive
positive integers, as in the OEIS definition (no bound on `k` or `m`). -/
theorem A109814_isGreatest {n : ℕ} (hn : 1 ≤ n) :
    IsGreatest {k | IsConsecSum n k} (A109814 n) := by
  constructor
  · have h1 : IsConsecSumBdd n 1 := ⟨n, by simp [hn], by simp⟩
    obtain ⟨m, hm, hs⟩ := Nat.findGreatest_spec (P := IsConsecSumBdd n) hn h1
    exact ⟨m, (Finset.mem_Icc.1 hm).1, hs⟩
  · rintro k ⟨m, hm, hs⟩
    have hk : k ≤ n := by
      have : ∑ _i ∈ range k, 1 ≤ ∑ i ∈ range k, (m + i) :=
        Finset.sum_le_sum (fun i _ => by omega)
      simpa [hs] using this
    have hk1 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hs; omega
      · exact h
    have hmn : m ≤ n := by
      have := Finset.single_le_sum (f := fun i => m + i) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.2 hk1)
      simp only [add_zero] at this
      omega
    exact Nat.le_findGreatest hk ⟨m, Finset.mem_Icc.2 ⟨hm, hmn⟩, hs⟩

/-- A109814 reproduces its first 40 listed terms (kernel-checked). -/
theorem A109814_data : (List.range 40).map (fun i => A109814 (i + 1)) =
    [1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 2, 3, 2, 4, 5, 1, 2, 4, 2, 5, 6, 4, 2, 3, 5, 4, 6, 7, 2, 5, 2,
      1, 6, 4, 7, 8, 2, 4, 6, 5] := by
  decide +kernel

/-- Conjecture 1: if `T(n,k) > 0` (for an entry of the triangle), then `T(n,k)` is the smallest
part of the partition of `n` into `k` consecutive parts. Conjecture 2: the last positive entry
of row `n` is in column `A109814(n)`. -/
def statement : Prop :=
  (∀ n k : ℕ, 1 ≤ n → InRow n k → 0 < T n k →
    (∃ p : n.Partition, HasConsecutiveParts k p) ∧
    ∀ p : n.Partition, HasConsecutiveParts k p → IsLeast {x | x ∈ p.parts} (T n k)) ∧
  (∀ n : ℕ, 1 ≤ n → IsGreatest {k | InRow n k ∧ 0 < T n k} (A109814 n))

end Math0.Statements.A211343
