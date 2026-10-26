/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A373359: the row lengths of the Schreier-set triangle (increasing rows) are A007895

Source: https://oeis.org/A373359, Paolo Xausa, Jun 04 2024 (CROSSREFS section). Verbatim:
> Cf. A007895 (conjectured row lengths), A373346 (row sums), A373347.

That is: row `n` of A373359 has length A007895(n), the number of terms in the Zeckendorf
representation of `n`.

## The OEIS definitions

* A373359 (offset `1`, keyword `tabf`): "Irregular triangle read by rows where row n lists (in
  increasing order) the elements of the Schreier set encoded by A371176(n)." The encoding (see
  A373345, to which the entry refers, and the example table of A373359) takes `k` to the set of
  the 1-based positions of the ones in the binary expansion of `k`, position 1 being the least
  significant bit. Example rows: row 4 (`A371176(4) = 6 = 110₂`) is `2, 3`; row 12
  (`A371176(12) = 28 = 11100₂`) is `3, 4, 5`.
* A371176 (offset `1`): "Numbers k such that A000120(k) <= A001511(k)", where A000120(k) is the
  binary weight of `k` (number of ones in its binary expansion) and A001511(k) is the ruler
  function, "the 2-adic valuation of 2n" (defined for `k ≥ 1`). Its terms start
  `1, 2, 4, 6, 8, 10, 12, 16, …`.
* A007895 (offset `0`): "Number of terms in the Zeckendorf representation of n (write n as a sum
  of non-consecutive distinct Fibonacci numbers)."

## Encoding

* `IsTerm k` is A371176-membership: `0 < k ∧ k.bitIndices.length ≤ padicValNat 2 (2 * k)`.
  Mathlib's `Nat.bitIndices k` is the increasing list of the (0-based) indices of the ones in the
  binary expansion of `k` (`Nat.mem_bitIndices : i ∈ k.bitIndices ↔ k.testBit i`), so its length
  is A000120(k); `padicValNat 2 (2 * k)` is A001511(k). The condition `0 < k` reflects that
  A371176 is a sequence of positive integers (A001511 is only defined for `k ≥ 1`; without it,
  `k = 0` would satisfy `0 ≤ 0`).
* `A371176 n = Nat.nth IsTerm (n - 1)` is the `n`-th term (offset `1`, so `n ≥ 1`).
* `T n` is row `n` of A373359: `(A371176 n).bitIndices.map (· + 1)`, i.e. the 1-based positions
  of the ones of `A371176 n`, in increasing order. Its length is the row length (the cardinality
  of the Schreier set). `T_ne_nil` shows every row is nonempty.
* `Nat.zeckendorf n` is Mathlib's Zeckendorf representation of `n`: the list of indices `i ≥ 2`
  (strictly decreasing, pairwise non-consecutive) with `n = ∑ fib i`. Its length is the number of
  terms in the Zeckendorf representation, i.e. A007895(n).
* *Alignment.* Row `n` of A373359 (`n ≥ 1`) is matched with A007895(n): this is the only reading
  consistent with the data (row 1 = `{1}` has length `1 = A007895(1)`, row 4 = `{2, 3}` has length
  `2 = A007895(4)`, row 12 = `{3, 4, 5}` has length `3 = A007895(12)`; matching row 1 with the
  first listed term A007895(0) = 0 would fail at once). `statement_check` kernel-checks the
  claimed equality for the rows `n = 1, …, 42` covered by the listed data, as a sanity check of
  this alignment.
* *Computation.* `Nat.bitIndices`, `Nat.nth` and `Nat.zeckendorf` are not suitable for kernel
  evaluation, so computable versions are used for the checks and proved equal to them:
  `bitPos_eq_bitIndices` (bits via `Nat.testBit` below `Nat.log2 k + 1`), `isTermB_iff` (the
  ruler function is one more than the lowest set-bit index), `code_eq_nth` (`code i`, obtained by
  `i` steps of a bounded search for the next term starting from `1`, equals `Nat.nth IsTerm i`;
  the search window `(k, 2k + 1]` always contains the power of two `2 ^ (log2 k + 1)`, a term),
  `row_eq_T`, and `zeckAux_eq` (fuel-bounded greedy Zeckendorf).
* `a m` is the flattened sequence (offset `1`): the `m`-th entry of `T 1 ++ T 2 ++ ⋯`. Since every
  row is nonempty, the first `m` rows already contain at least `m` entries, so
  `a m = ((List.range m).flatMap (fun i => T (i + 1))).getD (m - 1) 0` (`a_eq`). `a_data`
  checks all 91 listed terms `a 1, …, a 91` (rows 1 to 42).
* *The conjecture* (`statement`): for every `n ≥ 1`, `(T n).length = (Nat.zeckendorf n).length`.
-/

namespace Math0.Statements.A373359

/-! ### The OEIS definitions -/

/-- `k` is a term of A371176: `k ≥ 1` and A000120(k) ≤ A001511(k), i.e. the number of ones in the
binary expansion of `k` is at most the 2-adic valuation of `2k`. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ k.bitIndices.length ≤ padicValNat 2 (2 * k)

/-- A371176(n), the `n`-th term (offset `1`) of A371176. -/
noncomputable def A371176 (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Row `n` (`n ≥ 1`) of A373359: the elements of the Schreier set encoded by A371176(n), i.e. the
1-based positions of the ones in the binary expansion of A371176(n), in increasing order. -/
noncomputable def T (n : ℕ) : List ℕ := (A371176 n).bitIndices.map (· + 1)

/-! ### Kernel-computable versions -/

/-- The 0-based positions of the ones in the binary expansion of `k`, in increasing order. -/
def bitPos (k : ℕ) : List ℕ := (List.range (k.log2 + 1)).filter (fun i => k.testBit i)

theorem bitPos_eq_bitIndices (k : ℕ) : bitPos k = k.bitIndices := by
  apply List.SortedLT.eq_of_mem_iff
  · exact (List.pairwise_lt_range.filter _).sortedLT
  · exact Nat.bitIndices_sorted
  · intro i
    simp only [bitPos, List.mem_filter, List.mem_range, Nat.mem_bitIndices]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have hk : k ≠ 0 := by
        rintro rfl
        simp at h
      have := (Nat.le_log2 hk).2 (Nat.ge_two_pow_of_testBit h)
      omega

/-- A001511(k) is one more than the index of the lowest one bit of `k`. -/
theorem padicValNat_two_mul (k : ℕ) (hk : k ≠ 0) :
    padicValNat 2 (2 * k) = k.bitIndices.headD 0 + 1 := by
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk
  obtain ⟨m', rfl⟩ := hm
  have hb : (2 ^ v * (2 * m' + 1)).bitIndices.headD 0 = v := by
    rw [Nat.bitIndices_two_pow_mul, Nat.bitIndices_two_mul_add_one]
    simp
  rw [hb, show 2 * (2 ^ v * (2 * m' + 1)) = 2 ^ (v + 1) * (2 * m' + 1) by ring,
    padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega)]

/-- Boolean test for membership in A371176. -/
def isTermB (k : ℕ) : Bool :=
  decide (0 < k) && decide ((bitPos k).length ≤ (bitPos k).headD 0 + 1)

theorem isTermB_iff (k : ℕ) : isTermB k = true ↔ IsTerm k := by
  simp only [isTermB, IsTerm, Bool.and_eq_true, decide_eq_true_eq, bitPos_eq_bitIndices]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, by rw [padicValNat_two_mul k hk.ne']; exact h⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, by rw [padicValNat_two_mul k hk.ne'] at h; exact h⟩

instance : DecidablePred IsTerm := fun k => decidable_of_iff _ (isTermB_iff k)

theorem isTerm_two_pow (e : ℕ) : IsTerm (2 ^ e) := by
  refine ⟨by positivity, ?_⟩
  rw [Nat.bitIndices_two_pow, ← pow_succ', padicValNat.prime_pow]
  simp

/-- `search f s`: the first `j ∈ [s, s + f)` with `isTermB j`, or `s + f` if there is none. -/
def search : ℕ → ℕ → ℕ
  | 0, s => s
  | f + 1, s => if isTermB s then s else search f (s + 1)

theorem search_spec (f s : ℕ) (h : ∃ j, s ≤ j ∧ j < s + f ∧ isTermB j = true) :
    s ≤ search f s ∧ isTermB (search f s) = true ∧
      ∀ j, s ≤ j → j < search f s → isTermB j = false := by
  induction f generalizing s with
  | zero =>
    obtain ⟨j, h1, h2, _⟩ := h
    omega
  | succ f ih =>
    simp only [search]
    split_ifs with hs
    · exact ⟨le_rfl, hs, fun j h1 h2 => by omega⟩
    · have h' : ∃ j, s + 1 ≤ j ∧ j < s + 1 + f ∧ isTermB j = true := by
        obtain ⟨j, h1, h2, h3⟩ := h
        refine ⟨j, ?_, by omega, h3⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · exact absurd h3 hs
        · omega
      obtain ⟨ih1, ih2, ih3⟩ := ih (s + 1) h'
      refine ⟨by omega, ih2, fun j h1 h2 => ?_⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · simpa using hs
      · exact ih3 j h1 h2

/-- The least term of A371176 exceeding `k` (for `k ≥ 1`; see `nextTerm_spec`). -/
def nextTerm (k : ℕ) : ℕ := search (k + 1) (k + 1)

theorem nextTerm_spec (k : ℕ) (hk : 0 < k) :
    k < nextTerm k ∧ IsTerm (nextTerm k) ∧ ∀ j, k < j → j < nextTerm k → ¬ IsTerm j := by
  unfold nextTerm
  have hex : ∃ j, k + 1 ≤ j ∧ j < k + 1 + (k + 1) ∧ isTermB j = true := by
    refine ⟨2 ^ (k.log2 + 1), ?_, ?_, (isTermB_iff _).2 (isTerm_two_pow _)⟩
    · have := Nat.lt_log2_self (n := k)
      omega
    · have := Nat.log2_self_le hk.ne'
      rw [pow_succ]
      omega
  obtain ⟨h1, h2, h3⟩ := search_spec (k + 1) (k + 1) hex
  refine ⟨h1, (isTermB_iff _).1 h2, fun j hj1 hj2 => ?_⟩
  rw [← isTermB_iff, h3 j hj1 hj2]
  simp

theorem count_step (c c' : ℕ) (hc : IsTerm c) (hlt : c < c')
    (hno : ∀ j, c < j → j < c' → ¬ IsTerm j) :
    Nat.count IsTerm c' = Nat.count IsTerm c + 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, c' = c + d + 1 := ⟨c' - c - 1, by omega⟩
  induction d with
  | zero => rw [add_zero, Nat.count_succ, if_pos hc]
  | succ d ih =>
    rw [show c + (d + 1) + 1 = (c + d + 1) + 1 by ring, Nat.count_succ,
      ih (by omega) (fun j h1 h2 => hno j h1 (by omega)),
      if_neg (hno _ (by omega) (by omega))]

/-- `code i` is the `i`-th term (0-indexed) of A371176, computed by iterating `nextTerm`. -/
def code (i : ℕ) : ℕ := nextTerm^[i] 1

theorem code_spec (i : ℕ) : IsTerm (code i) ∧ Nat.count IsTerm (code i) = i := by
  induction i with
  | zero =>
    refine ⟨by simpa [code] using isTerm_two_pow 0, ?_⟩
    simp [code, Nat.count_succ, IsTerm]
  | succ i ih =>
    have hc : code (i + 1) = nextTerm (code i) := Function.iterate_succ_apply' _ _ _
    obtain ⟨h1, h2, h3⟩ := nextTerm_spec (code i) ih.1.1
    rw [hc]
    exact ⟨h2, by rw [count_step _ _ ih.1 h1 h3, ih.2]⟩

/-- The computed terms are the terms of A371176. -/
theorem code_eq_nth (i : ℕ) : code i = Nat.nth IsTerm i := by
  have h := Nat.nth_count (code_spec i).1
  rw [(code_spec i).2] at h
  exact h.symm

/-- Row of the triangle for the code `k`: the 1-based positions of the ones of `k`, increasing. -/
def rowOf (k : ℕ) : List ℕ := (bitPos k).map (· + 1)

/-- Computable version of row `n` of A373359. -/
def row (n : ℕ) : List ℕ := rowOf (code (n - 1))

theorem row_eq_T (n : ℕ) : row n = T n := by
  simp [row, rowOf, T, A371176, code_eq_nth, bitPos_eq_bitIndices]

/-- Every row is nonempty. -/
theorem T_ne_nil (n : ℕ) : T n ≠ [] := by
  have hpos := (code_spec (n - 1)).1.1
  rw [← row_eq_T]
  simp only [row, rowOf, bitPos_eq_bitIndices, ne_eq, List.map_eq_nil_iff]
  intro hnil
  have := Nat.sum_map_two_pow_bitIndices (code (n - 1))
  rw [hnil] at this
  simp at this
  omega

/-- `codesAux N k = [k, nextTerm k, …, nextTerm^[N-1] k]`. -/
def codesAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | N + 1, k => k :: codesAux N (nextTerm k)

theorem codesAux_eq (N k : ℕ) : codesAux N k = (List.range N).map (fun i => nextTerm^[i] k) := by
  induction N generalizing k with
  | zero => rfl
  | succ N ih =>
    rw [codesAux, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

/-- A373359 as a flattened sequence (offset `1`): `a m` is the `m`-th entry of
`T 1 ++ T 2 ++ T 3 ++ ⋯` (see `a_eq`). -/
def a (m : ℕ) : ℕ := ((codesAux m 1).flatMap rowOf).getD (m - 1) 0

theorem a_eq (m : ℕ) : a m = ((List.range m).flatMap (fun i => T (i + 1))).getD (m - 1) 0 := by
  rw [a, codesAux_eq, List.flatMap_map]
  congr 2
  funext i
  rw [← row_eq_T]
  rfl

/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all 91 listed
terms, i.e. rows 1 to 42. -/
theorem a_data : (List.range 91).map (fun i => a (i + 1)) =
    [1, 2, 3, 2, 3, 4, 2, 4, 3, 4, 5, 2, 5, 3, 5, 4, 5, 3, 4, 5, 6, 2, 6, 3, 6, 4, 6, 3, 4, 6, 5,
      6, 3, 5, 6, 4, 5, 6, 7, 2, 7, 3, 7, 4, 7, 3, 4, 7, 5, 7, 3, 5, 7, 4, 5, 7, 6, 7, 3, 6, 7, 4,
      6, 7, 5, 6, 7, 4, 5, 6, 7, 8, 2, 8, 3, 8, 4, 8, 3, 4, 8, 5, 8, 3, 5, 8, 4, 5, 8, 6, 8] := by
  decide +kernel

/-- The first terms of A371176 (data of that entry, `n = 1, …, 42`), kernel-checked. -/
theorem code_data : (List.range 42).map code =
    [1, 2, 4, 6, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 52, 56, 64, 66, 68, 72,
      76, 80, 84, 88, 96, 100, 104, 112, 120, 128, 130, 132, 136, 140, 144, 148, 152, 160] := by
  decide +kernel

/-! ### Zeckendorf representation, computably (for the sanity check only) -/

/-- Greedy Zeckendorf representation with fuel. -/
def zeckAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, m =>
    if m = 0 then [] else Nat.greatestFib m :: zeckAux f (m - Nat.fib (Nat.greatestFib m))

theorem zeckAux_eq (f m : ℕ) (h : m ≤ f) : zeckAux f m = Nat.zeckendorf m := by
  induction f generalizing m with
  | zero =>
    obtain rfl : m = 0 := by omega
    simp [zeckAux]
  | succ f ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [zeckAux]
    · have hfib : 0 < Nat.fib (Nat.greatestFib m) := Nat.fib_pos.2 (Nat.greatestFib_pos.2 hm)
      rw [zeckAux, if_neg hm.ne', Nat.zeckendorf_of_pos hm, ih _ (by omega)]

/-- Sanity check of the alignment of rows with A007895: the claimed equality holds for the rows
`n = 1, …, 42` covered by the listed data. -/
theorem statement_check : ∀ n, 1 ≤ n → n ≤ 42 → (T n).length = (Nat.zeckendorf n).length := by
  have h : (List.range 42).all
      (fun i => (row (i + 1)).length == (zeckAux (i + 1) (i + 1)).length) = true := by
    decide +kernel
  intro n h1 h2
  rw [← row_eq_T, ← zeckAux_eq n n le_rfl]
  rw [List.all_eq_true] at h
  have := h (n - 1) (List.mem_range.2 (by omega))
  rw [show n - 1 + 1 = n by omega] at this
  simpa using this

/-! ### The conjecture -/

/-- OEIS A373359 (Paolo Xausa, CROSSREFS: "A007895 (conjectured row lengths)"): for every
`n ≥ 1`, row `n` of the triangle (the Schreier set encoded by A371176(n), listed in increasing
order) has as many elements as there are terms in the Zeckendorf representation of `n`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → (T n).length = (Nat.zeckendorf n).length

end Math0.Statements.A373359
