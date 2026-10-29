/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A388724: strictly superdiagonal reversed partitions by maximum

Source: https://oeis.org/A388724, _Gus Wiseman_, Sep 24 2025 (FORMULA section). Verbatim:
> Conjecture: Column sums are A000245.

The entry (offset `0`, keywords `nonn,tabl`) is "Triangle read by rows where T(n,k) is the number
of strictly superdiagonal reversed integer partitions of n with maximum k.", with the comment
"A sequence (y_1, ..., y_k) is strictly superdiagonal iff y_i > i for all i = 1..k." Its
Mathematica program counts `Reverse /@ IntegerPartitions[n]` (the partitions of `n` listed in
weakly increasing order) with `Max @@ # == k` and `y_i > i` for every position `i`, for
`0 ≤ k ≤ n`.

A000245 (N. J. A. Sloane, offset `0`) is "a(n) = 3*(2*n)!/((n+2)!*(n-1)!)." with data
`0, 1, 3, 9, 28, 90, …`.

## Encoding

* *Reversed partitions.* A reversed integer partition of `n` is its multiset of parts listed in
  weakly increasing order, i.e. a list `y = [y_1, …, y_m]` of positive integers with
  `y_1 ≤ … ≤ y_m` and `y_1 + … + y_m = n` (`IsRevPartition n y`); each partition of `n`
  corresponds to exactly one such list. The empty list is the reversed partition of `0`.
* *Strictly superdiagonal.* `y_i > i` for every position `i = 1, …, m`; with 0-indexed
  `y[i] = y_{i+1}` this is `i + 1 < y[i]` for every `i < m` (`StrictlySuperdiagonal y`).
* *Maximum.* "With maximum `k`" is `y.max? = some k`. The empty partition of `0` has no maximum
  (Mathematica's `Max[]` is `-Infinity`), so it is not counted for any `k`, which agrees with
  the listed `T(0,0) = 0`.
* *The triangle.* `T n k` is the number (`Set.ncard`) of lists `y` that are reversed partitions
  of `n`, strictly superdiagonal and have maximum `k`. It is defined for all `n, k`; outside the
  triangle (`k > n`) it is `0` since the maximum part is at most the sum. The set is finite
  (`T_eq_Tc` identifies it with a filtered finite list), so `Set.ncard` is its true size.
  `a i` is the triangle read by rows with offset `0`: row `n` occupies the positions
  `n(n+1)/2, …, n(n+1)/2 + n`, and its entries are `T(n,0), …, T(n,n)` (`rowOf i` is the row of
  position `i`, the largest `n` with `n(n+1)/2 ≤ i`).
* *Computation.* `gen fuel lo n` enumerates the weakly increasing lists of integers `≥ lo`
  with sum `n` (`mem_gen`, for `lo ≥ 1` and `n ≤ fuel`) without repetitions (`nodup_gen`), and
  `T_eq_Tc` rewrites `T` as the length of a filter of `gen n 1 n`. `a_data` checks all 78 listed
  terms (rows `0..11`) in the kernel.
* *A000245.* `A000245 n = 3 * (2n)! / ((n+2)! * (n-1)!)` for `n ≥ 1` (an exact division) and
  `A000245 0 = 0`, as listed (the formula's `(-1)!` is infinite at `n = 0`). `A000245_data`
  checks the first 28 listed terms.
* *The conjecture.* Column `k` of the triangle consists of the entries `T(n,k)`, `n ≥ k`; its
  sum is `∑ᶠ n, T n k` (only finitely many terms are nonzero: `T n k = 0` for `n > k(k-1)`,
  `T_eq_zero_of_lt`, so this is an honest finite sum, `colSum_eq`). The column sums are
  `0, 0, 1, 3, 9, 28, 90, …` for `k = 0, 1, 2, …`, and "Column sums are A000245" is read with the
  only alignment matching the listed values: the sum of column `k` is `A000245(k-1)` for every
  `k ≥ 1` (column `0` is identically zero and is an extra leading `0`; nothing is claimed about
  it). `statement_check` verifies this for `k = 1, …, 5` in the kernel (column sums
  `0, 1, 3, 9, 28`; the naive enumeration of all partitions of `n ≤ 30` needed for `k = 6`
  exhausts the kernel's memory).
-/

namespace Math0.Statements.A388724

open Finset

/-! ### Definitions -/

/-- `y` is a reversed integer partition of `n`: a list of positive integers in weakly increasing
order with sum `n`. -/
def IsRevPartition (n : ℕ) (y : List ℕ) : Prop :=
  (∀ x ∈ y, 0 < x) ∧ y.Pairwise (· ≤ ·) ∧ y.sum = n

/-- `y = (y_1, …, y_m)` is strictly superdiagonal: `y_i > i` for all `i = 1..m` (0-indexed:
`y[i] > i + 1` for `i < m`). -/
def StrictlySuperdiagonal (y : List ℕ) : Prop := ∀ i (h : i < y.length), i + 1 < y[i]

instance : DecidablePred StrictlySuperdiagonal := fun y => by
  unfold StrictlySuperdiagonal
  infer_instance

/-- A388724 as a triangle: `T(n,k)` is the number of strictly superdiagonal reversed integer
partitions of `n` with maximum `k`. -/
noncomputable def T (n k : ℕ) : ℕ :=
  {y : List ℕ | IsRevPartition n y ∧ StrictlySuperdiagonal y ∧ y.max? = some k}.ncard

/-- The row of position `i` in the triangle read by rows (offset `0`): the largest `n` with
`n(n+1)/2 ≤ i`. -/
def rowOf (i : ℕ) : ℕ := Nat.findGreatest (fun n => n * (n + 1) / 2 ≤ i) i

/-- A388724: the triangle `T(n,k)`, `0 ≤ k ≤ n`, read by rows (offset `0`). -/
noncomputable def a (i : ℕ) : ℕ := T (rowOf i) (i - rowOf i * (rowOf i + 1) / 2)

/-- A000245: `a(n) = 3*(2*n)!/((n+2)!*(n-1)!)`, with `a(0) = 0`. -/
def A000245 (n : ℕ) : ℕ :=
  if n = 0 then 0 else 3 * (2 * n).factorial / ((n + 2).factorial * (n - 1).factorial)

/-! ### Enumerating reversed partitions -/

/-- The weakly increasing lists of integers `≥ lo` with sum `n` (correct when `1 ≤ lo` and
`n ≤ fuel`, see `mem_gen`): the first entry is some `j ∈ [lo, n]`, followed by such a list with
entries `≥ j` and sum `n - j`. -/
def gen : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, n => if n = 0 then [[]] else []
  | fuel + 1, lo, n =>
    if n = 0 then [[]] else
      (List.range' lo (n + 1 - lo)).flatMap fun j => (gen fuel j (n - j)).map (j :: ·)

theorem eq_nil_of_sum_eq_zero {lo : ℕ} {y : List ℕ} (hlo : 1 ≤ lo) (h : ∀ x ∈ y, lo ≤ x)
    (hs : y.sum = 0) : y = [] := by
  cases y with
  | nil => rfl
  | cons x t =>
    have hx := h x List.mem_cons_self
    simp only [List.sum_cons] at hs
    omega

theorem mem_gen : ∀ (fuel lo n : ℕ) (y : List ℕ), 1 ≤ lo → n ≤ fuel →
    (y ∈ gen fuel lo n ↔ (∀ x ∈ y, lo ≤ x) ∧ y.Pairwise (· ≤ ·) ∧ y.sum = n)
  | 0, lo, n, y, hlo, hn => by
    have hn0 : n = 0 := by omega
    subst hn0
    simp only [gen, if_true, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h1, -, h3⟩
      exact eq_nil_of_sum_eq_zero hlo h1 h3
  | fuel + 1, lo, n, y, hlo, hn => by
    by_cases hn0 : n = 0
    · subst hn0
      simp only [gen, if_true, List.mem_singleton]
      constructor
      · rintro rfl
        simp
      · rintro ⟨h1, -, h3⟩
        exact eq_nil_of_sum_eq_zero hlo h1 h3
    · simp only [gen, if_neg hn0, List.mem_flatMap, List.mem_range'_1, List.mem_map]
      constructor
      · rintro ⟨j, ⟨h1, h2⟩, t, ht, rfl⟩
        rw [mem_gen fuel j (n - j) t (by omega) (by omega)] at ht
        obtain ⟨ht1, ht2, ht3⟩ := ht
        simp only [List.mem_cons, forall_eq_or_imp, List.pairwise_cons, List.sum_cons]
        exact ⟨⟨h1, fun x hx => le_trans h1 (ht1 x hx)⟩, ⟨ht1, ht2⟩, by omega⟩
      · rintro ⟨h1, h2, h3⟩
        cases y with
        | nil => simp at h3; omega
        | cons x t =>
          simp only [List.mem_cons, forall_eq_or_imp, List.pairwise_cons, List.sum_cons]
            at h1 h2 h3
          refine ⟨x, ⟨h1.1, by omega⟩, t, ?_, rfl⟩
          rw [mem_gen fuel x (n - x) t (by omega) (by omega)]
          exact ⟨h2.1, h2.2, by omega⟩

theorem nodup_gen : ∀ (fuel lo n : ℕ), (gen fuel lo n).Nodup
  | 0, lo, n => by
    unfold gen
    split <;> simp
  | fuel + 1, lo, n => by
    unfold gen
    split
    · simp
    · rw [List.nodup_flatMap]
      refine ⟨fun j _ => (nodup_gen fuel j (n - j)).map List.cons_injective, ?_⟩
      refine (List.nodup_range' (s := lo) (n := n + 1 - lo)).imp fun {i j} hij => ?_
      intro y hy1 hy2
      simp only [List.mem_map] at hy1 hy2
      obtain ⟨t, -, rfl⟩ := hy1
      obtain ⟨t', -, h⟩ := hy2
      exact hij (List.cons.inj h).1.symm

/-- Computable version of `T` (see `T_eq_Tc`). -/
def Tc (n k : ℕ) : ℕ :=
  ((gen n 1 n).filter fun y => decide (StrictlySuperdiagonal y ∧ y.max? = some k)).length

theorem T_eq_Tc (n k : ℕ) : T n k = Tc n k := by
  have hset : {y : List ℕ | IsRevPartition n y ∧ StrictlySuperdiagonal y ∧ y.max? = some k} =
      ↑((gen n 1 n).filter fun y => decide (StrictlySuperdiagonal y ∧ y.max? = some k)).toFinset
      := by
    ext y
    simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_filter, decide_eq_true_eq,
      mem_gen n 1 n y le_rfl le_rfl, IsRevPartition, Nat.one_le_iff_ne_zero,
      Nat.pos_iff_ne_zero]
  rw [T, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup ((nodup_gen n 1 n).filter _),
    Tc]

/-! ### Columns are finite -/

/-- A strictly superdiagonal reversed partition with maximum `k` has fewer than `k` parts, all at
most `k`, so its sum is at most `k(k-1)`. -/
theorem T_eq_zero_of_lt {n k : ℕ} (h : k * (k - 1) < n) : T n k = 0 := by
  have hempty : {y : List ℕ | IsRevPartition n y ∧ StrictlySuperdiagonal y ∧
      y.max? = some k} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro y ⟨⟨-, -, hsum⟩, hss, hmax⟩
    rw [List.max?_eq_some_iff] at hmax
    obtain ⟨hk, hle⟩ := hmax
    have hpos : 0 < y.length := List.length_pos_of_mem hk
    have hlast := hss (y.length - 1) (by omega)
    have hlen : y.length + 1 ≤ k := by
      have hmem : y[y.length - 1]'(by omega) ∈ y := List.getElem_mem _
      have := hle _ hmem
      omega
    have hs : y.sum ≤ y.length * k := by
      simpa using List.sum_le_card_nsmul y k hle
    have : y.length * k ≤ (k - 1) * k := Nat.mul_le_mul_right k (by omega)
    rw [Nat.mul_comm (k - 1) k] at this
    omega
  rw [T, hempty, Set.ncard_empty]

/-- The column sum `∑ᶠ n, T n k` is the finite sum over `n ≤ k(k-1)`. -/
theorem colSum_eq (k : ℕ) : ∑ᶠ n, T n k = ∑ n ∈ range (k * (k - 1) + 1), T n k := by
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Function.mem_support, ne_eq, coe_range, Set.mem_Iio] at hn ⊢
  by_contra hlt
  exact hn (T_eq_zero_of_lt (by omega))

/-! ### Data checks -/

theorem a_eq (i : ℕ) :
    a i = Tc (rowOf i) (i - rowOf i * (rowOf i + 1) / 2) := by
  rw [a, T_eq_Tc]

/-- The definition reproduces all 78 terms listed in OEIS (rows `0..11`; kernel-checked). -/
theorem a_data : (List.range 78).map (fun i => a i) =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0,
      0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 2,
      2, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 2, 2, 1, 1, 1, 0, 1] := by
  simp only [a_eq]
  decide +kernel

/-- A000245: the first 28 listed terms (kernel-checked). -/
theorem A000245_data : (List.range 28).map A000245 =
    [0, 1, 3, 9, 28, 90, 297, 1001, 3432, 11934, 41990, 149226, 534888, 1931540, 7020405,
      25662825, 94287120, 347993910, 1289624490, 4796857230, 17902146600, 67016296620,
      251577050010, 946844533674, 3572042254128, 13505406670700, 51166197843852,
      194214400834356] := by
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Wiseman, A388724): the column sums of the triangle are A000245, i.e. for every
`k ≥ 1`, the sum over all `n` of `T(n,k)` (the number of strictly superdiagonal reversed integer
partitions, of any size, with maximum `k`) equals `A000245(k-1)`. -/
def statement : Prop := ∀ k : ℕ, 1 ≤ k → ∑ᶠ n, T n k = A000245 (k - 1)

/-- Sanity check: the conjecture holds for the columns `k = 1, …, 5` (column sums
`0, 1, 3, 9, 28`; kernel-checked). -/
theorem statement_check : ∀ k : ℕ, 1 ≤ k → k ≤ 5 → ∑ᶠ n, T n k = A000245 (k - 1) := by
  have h : (List.range 5).map (fun j => ∑ n ∈ range ((j + 1) * j + 1), Tc n (j + 1)) =
      (List.range 5).map A000245 := by
    decide +kernel
  intro k hk1 hk2
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : j < 5 := by omega
  have := congrArg (fun l => l[j]?) h
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq]
    at this
  rw [colSum_eq, Nat.add_sub_cancel]
  simpa [T_eq_Tc] using this

end Math0.Statements.A388724
