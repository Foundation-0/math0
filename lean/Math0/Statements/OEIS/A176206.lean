/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A176206: divisors of the row terms versus the parts of the partitions of `n`

Source: https://oeis.org/A176206, _Omar E. Pol_, Nov 23 2020 (COMMENTS section). Verbatim:
> Conjecture: all divisors of all terms in row n are also all parts of all partitions of n.

The entry (_Alford Arnold_, Apr 11 2010; new name, offset and terms by _Omar E. Pol_,
Nov 22 2020; keyword `tabf`, offset `1`) is "Irregular triangle T(n,k) (n >= 1, k >= 1) read by
rows: row n has length A000070(n-1) and every column k gives the positive integers." Its comments
make this explicit: "Row n contains a decreasing sequence where n-k is repeated A000041(k) times,
k = 0..n-1", which is also the Mathematica program
`Table[Flatten[Table[ConstantArray[n-k,PartitionsP[k]],{k,0,n-1}]],{n,10}]`.

## Encoding

* `p k` is the partition number A000041(k), defined as the number of `Nat.Partition k`
  (multisets of positive integers summing to `k`). It is not kernel-friendly, so we also define a
  structurally recursive count `pb n m` of the partitions of `n` with all parts `≤ m` and prove
  `p k = pb k k` (`p_eq_pb`); this is only used to evaluate the data.
* `row n` is row `n` of the triangle: `n, n-1, …, 1`, where `n - k` is repeated `p k` times,
  for `k = 0, …, n-1` (so `row 0 = []`). We prove the two properties in the entry's name:
  `length_row` (row `n` has length `∑_{k<n} p k = A000070(n-1)`) and `row_succ`
  (`row (n+1)` is `row n` with every entry increased by `1`, followed by `p n` ones), which is
  exactly "every column `k` gives the positive integers": the column of `k` starts with a `1` in
  the first row of length `≥ k` and grows by `1` from one row to the next.
* `T n k` is the `k`-th entry (`1 ≤ k ≤ A000070(n-1)`) of row `n`, and `a` is the flattened
  sequence with the OEIS indexing (`a 1, a 2, …`). `a_data` checks all 94 listed terms
  (rows `1` to `7` and the first 19 terms of row `8`) in the kernel, and `row_five_divisors`
  checks the divisor count of the entry's example for `n = 5` (left-hand side only: the
  enumeration of `Nat.Partition n` is too slow for the kernel).
* The conjecture is read as an identity of multisets, as the entry's worked example for `n = 5`
  makes clear (on both sides "there are twelve 1's, four 2's, two 3's, one 4 and one 5"): the
  multiset of all divisors of all terms of row `n`, counted with multiplicity (each term `t`
  contributes every divisor of `t` once, and every term of the row counts), equals the multiset
  of all parts of all partitions of `n` (each partition of `n` contributes all of its parts, with
  multiplicity). It is stated for every row, i.e. every `n ≥ 1`.
-/

namespace Math0.Statements.A176206

/-! ### Partition numbers -/

/-- The partition number A000041(k): the number of partitions of `k`. -/
def p (k : ℕ) : ℕ := Fintype.card (Nat.Partition k)

/-- The number of partitions of `n` all of whose parts are `≤ m`. -/
def B (n m : ℕ) : ℕ :=
  (Finset.univ.filter (fun π : n.Partition => ∀ i ∈ π.parts, i ≤ m)).card

/-- A computable count of the partitions of `n` into parts `≤ m` (`j` is the number of parts
equal to `m + 1`); `pb_eq_B` shows `pb n m = B n m`. -/
def pb : ℕ → ℕ → ℕ
  | n, 0 => if n = 0 then 1 else 0
  | n, m + 1 => ∑ j ∈ Finset.range (n / (m + 1) + 1), pb (n - j * (m + 1)) m

theorem part_le {n : ℕ} (π : n.Partition) {i : ℕ} (hi : i ∈ π.parts) : i ≤ n :=
  (Multiset.le_sum_of_mem hi).trans_eq π.parts_sum

theorem B_zero (m : ℕ) : B 0 m = 1 := by
  rw [B, Finset.filter_true_of_mem (by simp), Finset.card_univ, Fintype.card_unique]

theorem B_succ_zero (n : ℕ) : B (n + 1) 0 = 0 := by
  rw [B, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro π _ h
  have h0 : π.parts = 0 := Multiset.eq_zero_of_forall_notMem fun i hi => by
    have := π.parts_pos hi; have := h i hi; omega
  have := π.parts_sum
  rw [h0] at this
  simp at this

theorem B_succ (n m : ℕ) :
    B n (m + 1) = B n m + if m + 1 ≤ n then B (n - (m + 1)) (m + 1) else 0 := by
  rw [B, ← Finset.card_filter_add_card_filter_not
    (fun π : n.Partition => m + 1 ∈ π.parts), add_comm]
  congr 1
  · rw [B, Finset.filter_filter]
    congr 1
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hm⟩ i hi
      have := h i hi
      have : i ≠ m + 1 := fun e => hm (e ▸ hi)
      omega
    · intro h
      exact ⟨fun i hi => (h i hi).trans (Nat.le_succ m), fun hm => by have := h _ hm; omega⟩
  · split_ifs with hmn
    · rw [B]
      let e := Nat.Partition.partitionWithPartEquiv (n := n) (a := m + 1) (by omega) hmn
      refine Finset.card_bij' (fun π hπ => e ⟨π, (Finset.mem_filter.1 hπ).2⟩)
        (fun π _ => (e.symm π).1) ?_ ?_ ?_ ?_
      · intro π hπ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
        intro i hi
        rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at hi
        exact hπ.1 i (Multiset.mem_of_mem_erase hi)
      · intro π _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts]
        refine ⟨fun i hi => ?_, Multiset.mem_cons_self _ _⟩
        rcases Multiset.mem_cons.1 hi with rfl | hi
        · exact le_rfl
        · have h := Finset.mem_filter.1 ‹_›
          exact h.2 i hi
      · intro π _
        simp only [Equiv.symm_apply_apply]
      · intro π _
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro π _ h
      exact hmn (part_le π h)

theorem pb_zero_right (n : ℕ) : pb n 0 = if n = 0 then 1 else 0 := by
  rw [pb]

theorem pb_succ (n m : ℕ) :
    pb n (m + 1) = pb n m + if m + 1 ≤ n then pb (n - (m + 1)) (m + 1) else 0 := by
  rw [pb, Finset.sum_range_succ', add_comm]
  simp only [zero_mul, Nat.sub_zero]
  congr 1
  split_ifs with hmn
  · rw [pb, Nat.div_eq_sub_div (by omega) hmn]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [Nat.succ_mul]
    omega
  · rw [Nat.div_eq_of_lt (by omega)]
    simp

theorem pb_eq_B (n : ℕ) : ∀ m, pb n m = B n m := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro m
    induction m with
    | zero =>
      rcases n with _ | n
      · rw [pb_zero_right, B_zero]; rfl
      · rw [pb_zero_right, B_succ_zero]; simp
    | succ m ihm =>
      rw [pb_succ, B_succ, ihm]
      split_ifs with hmn
      · rw [ihn _ (by omega)]
      · rfl

/-- The partition numbers can be computed with `pb`. -/
theorem p_eq_pb (k : ℕ) : p k = pb k k := by
  rw [pb_eq_B, B, Finset.filter_true_of_mem (fun π _ i hi => part_le π hi), Finset.card_univ, p]

/-! ### The triangle -/

/-- Row `n` built from a sequence `f` of multiplicities: `n - k` repeated `f k` times, for
`k = 0, …, n-1`. -/
def rowOf (f : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).flatMap fun k => List.replicate (f k) (n - k)

/-- Row `n` of A176206: `n - k` repeated `A000041(k)` times, for `k = 0, …, n-1`. -/
def row (n : ℕ) : List ℕ := rowOf p n

/-- Row `n` has length A000070(n-1) `= ∑_{k=0}^{n-1} A000041(k)`. -/
theorem length_row (n : ℕ) : (row n).length = ∑ k ∈ Finset.range n, p k := by
  simp only [row, rowOf, List.length_flatMap, List.length_replicate]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- Row `n + 1` is row `n` with all entries increased by `1`, followed by `A000041(n)` ones:
every column of the triangle lists the positive integers. -/
theorem row_succ (n : ℕ) : row (n + 1) = (row n).map (· + 1) ++ List.replicate (p n) 1 := by
  simp only [row, rowOf, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.map_flatMap, List.map_replicate,
    Nat.add_sub_cancel_left]
  congr 1
  refine List.flatMap_congr fun k hk => ?_
  rw [List.mem_range] at hk
  congr 1
  omega

/-- `T n k`, the `k`-th term of row `n` (`n ≥ 1`, `1 ≤ k ≤ A000070(n-1)`). -/
def T (n k : ℕ) : ℕ := (row n).getD (k - 1) 0

/-- Read the flattened triangle (rows given by `r`) from row `n` on, skipping `j` terms; `fuel`
bounds the number of rows visited (every row `n ≥ 1` is nonempty, so `fuel = i` suffices for the
`i`-th term). -/
def flatAux (r : ℕ → List ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, n, j =>
    if j < (r n).length then (r n).getD j 0 else flatAux r fuel (n + 1) (j - (r n).length)

/-- A176206 as a sequence (the triangle read by rows), with the OEIS indexing: `a 1, a 2, …`. -/
def a (i : ℕ) : ℕ := flatAux row i 1 (i - 1)

/-- The definition reproduces all 94 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 94).map (fun i => a (i + 1)) =
    [1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 5, 4, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 6, 5, 4, 4,
      3, 3, 3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 6, 5, 5, 4, 4, 4, 3, 3, 3, 3, 3, 2, 2, 2,
      2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 3, 3, 3,
      3, 3, 3, 3] := by
  have hr : row = rowOf (fun k => pb k k) := funext fun n => by
    rw [row, show p = (fun k => pb k k) from funext p_eq_pb]
  simp only [a, hr]
  decide +kernel

/-- Sanity check of the left-hand side against the entry's worked example for `n = 5`: the
divisors of the terms of row 5 are twelve 1's, four 2's, two 3's, one 4 and one 5
(kernel-checked). -/
theorem row_five_divisors : ((row 5 : Multiset ℕ).bind fun t => t.divisors.val) =
    Multiset.replicate 12 1 + Multiset.replicate 4 2 + Multiset.replicate 2 3 + {4, 5} := by
  rw [row, show p = (fun k => pb k k) from funext p_eq_pb]
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Omar E. Pol, A176206): for every row `n ≥ 1`, the multiset of all divisors of
all terms of row `n` (each term contributing each of its divisors once) equals the multiset of
all parts of all partitions of `n`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (row n : Multiset ℕ).bind (fun t => t.divisors.val) =
      (Finset.univ : Finset n.Partition).val.bind (fun π => π.parts)

end Math0.Statements.A176206
