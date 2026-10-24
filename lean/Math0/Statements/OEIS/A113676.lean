/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A113676: Golomb's sequence (one 2 removed) cut into a triangle, and Levine's sequence

Source: https://oeis.org/A113676, Floor van Lamoen and Paul D. Hanna, Nov 06 2005 (COMMENTS
section). Verbatim:
> Conjecture: a(n) for n>1 gives first differences of Lionel Levine's sequence A014644(n) for n>=3.
> Conjecture: Final elements of the rows form A014644 except for duplicate 2.

The entry's name: "Number of elements of rows of Golomb's sequence A001462, with one less 2,
interpreted as triangle: Start with first row 1. The row sum of row n-1 gives the number of
elements taken from A001642 (one less 2) of row n." ("A001642" is a typo for A001462: the
example rows `1; 2; 3,3; 4,4,4,5,5,5; …` are Golomb's sequence `1, 2, 2, 3, 3, 4, …` with one
`2` removed.) Offset `1`; the listed terms are `1, 1, 2, 6, 27, 234, 6202, 1084009, 4362192095`.

## Encoding

* Golomb's sequence A001462 ("a(n) is the number of times n occurs in the sequence, starting
  with a(1) = 1", nondecreasing) is `golomb` (offset `1`; `golomb 0 = 0` is a junk value). It is
  computed by its self-generating construction `golombAux`: start from `1, 2, 2` and, for
  `k = 3, 4, …`, append `k` repeated `G(k)` times, where `G(k)` is read off the list built so far.
  `golombAux_eq_flatMap` proves that every stage is `1^G(1) 2^G(2) ⋯ (m+2)^G(m+2)` (each `k`
  repeated `golomb k` times, in increasing order), and `golomb_eq_getD` that `golomb` reads the
  stages consistently: this is exactly the self-describing property of A001462.
  `golomb_data` checks all 84 terms listed in A001462.
* `H` is Golomb's sequence with one less `2`: `H 1 = 1` and `H j = golomb (j + 1)` for `j ≥ 2`,
  i.e. `1, 2, 3, 3, 4, 4, 4, 5, 5, 5, …` (both `2`s are equal, so it does not matter which one
  is deleted).
* The triangle: `rowEnd n` is the number of terms of `H` used by rows `1, …, n`, and
  `row n` is the list of consecutive terms `H j` with `rowEnd (n - 1) < j ≤ rowEnd n`. Row `1`
  has one element, and the number of elements of row `n + 2` is the sum of row `n + 1`
  (`row_one`, `length_row_succ_succ`). `rows_example` checks the four rows shown in the entry.
  The sequence is `a n = (row n).length` (offset `1`); `a_data` kernel-checks all 9 listed terms
  `a 1, …, a 9`. (Rows `1, …, 7` use `H 1, …, H 6473`, and row `8` ends at `H 1090482`. To make
  this checkable, the proofs read Golomb's sequence from the faster `golombFast`, which is proved
  to give prefixes of `golomb` (`golombFast_eq_golombAux`, `map_H_range'`, `rowPairL_eq`); `a 9`
  is obtained from a weighted sum of the first `6474` terms (`a_nine`).) `rowLast_data` checks
  that the last elements of rows `1, …, 7` are `1, 2, 3, 5, 11, 38, 272`.
* Levine's sequence A014644 ("Form array starting with {1,1}; then i-th term in a row gives
  number of i's in next row; sequence is formed from final term in each row.", offset `1`):
  `levineRow 1 = [1, 1]`, and `levineRow (k + 1)` lists `1` `c₁` times, then `2` `c₂` times, …,
  where `levineRow k = [c₁, c₂, …]` (in increasing order, as in A014643, whose row 5 is
  `1,2,2,3,3,4,4,4,5,5,5`). `A014644 k` is the final term of `levineRow k`. `A014644_data`
  kernel-checks the first 11 listed terms `1, 2, 2, 3, 5, 11, 38, 272, 6474, 1090483,
  4363282578`.
* First conjecture: "a(n) for n>1 gives first differences of A014644(n) for n>=3" is read as
  `a n = A014644 (n + 2) - A014644 (n + 1)` for every `n ≥ 2` (so `a 2` is the first difference
  `A014644 4 - A014644 3` of A014644 taken from its third term on). It is stated in `ℤ`, so the
  subtraction is the true difference.
* Second conjecture: the final elements of rows `1, 2, 3, …` are A014644 `= 1, 2, 2, 3, 5, …`
  with one of its two equal terms `A014644 2 = A014644 3 = 2` removed, i.e. the last element of
  row `1` is `A014644 1` and the last element of row `n` is `A014644 (n + 1)` for every `n ≥ 2`.
  "The last element of row `n` is `x`" is `(row n).getLast? = some x`.
* `statement` is the conjunction of the two conjectures.
-/

namespace Math0.Statements.A113676

/-! ### Golomb's sequence A001462 -/

/-- Self-generating construction of Golomb's sequence: start from `1, 2, 2` and, for
`k = 3, …, m + 2`, append `k` repeated `G(k)` times, where `G(k)` is the `k`-th term (list index
`k - 1`) of the list built so far. -/
def golombAux : ℕ → List ℕ
  | 0 => [1, 2, 2]
  | m + 1 => golombAux m ++ List.replicate ((golombAux m).getD (m + 2) 0) (m + 3)

/-- Golomb's sequence A001462 (offset `1`): `golomb (n + 1)` is the term at list index `n` of
`golombAux n`. (`golomb 0 = 0` is a junk value.) -/
def golomb : ℕ → ℕ
  | 0 => 0
  | n + 1 => (golombAux n).getD n 0

/-- Golomb's sequence with one less `2` (offset `1`): `1, 2, 3, 3, 4, 4, 4, 5, 5, 5, …`, i.e.
`H 1 = golomb 1 = 1` and `H j = golomb (j + 1)` for `j ≥ 2`. (`H 0 = 0` is a junk value.) -/
def H (j : ℕ) : ℕ := if j ≤ 1 then golomb j else golomb (j + 1)

/-! ### The triangle and A113676 -/

/-- `rowEnd n` is the number of terms of `H` used by rows `1, …, n` of the triangle: row `1` has
one element, and row `n + 2` has as many elements as the sum of row `n + 1`, which consists of
the terms `H j` with `rowEnd n < j ≤ rowEnd (n + 1)`. -/
def rowEnd : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => rowEnd (n + 1) +
      ((List.range' (rowEnd n + 1) (rowEnd (n + 1) - rowEnd n)).map H).sum

/-- Row `n` (`n ≥ 1`) of the triangle: the consecutive terms `H j`,
`rowEnd (n - 1) < j ≤ rowEnd n`. -/
def row (n : ℕ) : List ℕ :=
  (List.range' (rowEnd (n - 1) + 1) (rowEnd n - rowEnd (n - 1))).map H

/-- A113676 (offset `1`): the number of elements of row `n` of the triangle. -/
def a (n : ℕ) : ℕ := (row n).length

/-! ### Levine's sequence A014644 -/

/-- `levineAux [c₀, c₁, …, c_r] i` is `i` repeated `c₀` times, then `i + 1` repeated `c₁` times,
…, then `i + r` repeated `c_r` times. -/
def levineAux : List ℕ → ℕ → List ℕ
  | [], _ => []
  | c :: l, i => List.replicate c i ++ levineAux l (i + 1)

/-- Row `k` (`k ≥ 1`) of Levine's array (A014643): row `1` is `[1, 1]`, and the `i`-th term of
row `k` is the number of `i`s in row `k + 1` (listed in increasing order).
(`levineRow 0 = []` is a junk value.) -/
def levineRow : ℕ → List ℕ
  | 0 => []
  | 1 => [1, 1]
  | k + 2 => levineAux (levineRow (k + 1)) 1

/-- Lionel Levine's sequence A014644 (offset `1`): the final term of row `k` of Levine's
array. -/
def A014644 (k : ℕ) : ℕ := (levineRow k).getLastD 0

/-! ### Basic facts about the definitions -/

theorem golombAux_succ (m : ℕ) :
    golombAux (m + 1) = golombAux m ++ List.replicate ((golombAux m).getD (m + 2) 0) (m + 3) :=
  rfl

theorem golombAux_prefix {m m' : ℕ} (h : m ≤ m') : golombAux m <+: golombAux m' := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (List.prefix_append _ _)

theorem golombAux_pos_length (m : ℕ) :
    (∀ x ∈ golombAux m, 1 ≤ x) ∧ m + 3 ≤ (golombAux m).length := by
  induction m with
  | zero => decide
  | succ m ih =>
    obtain ⟨hpos, hlen⟩ := ih
    have hmem : (golombAux m).getD (m + 2) 0 ∈ golombAux m := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have h1 := hpos _ hmem
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [golombAux_succ, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hpos x hx
      · rw [List.eq_of_mem_replicate hx]; omega
    · rw [golombAux_succ, List.length_append, List.length_replicate]; omega

/-- `golomb` reads every stage of the construction consistently. -/
theorem golomb_eq_getD {m j : ℕ} (hj : j < (golombAux m).length) :
    golomb (j + 1) = (golombAux m).getD j 0 := by
  show (golombAux j).getD j 0 = _
  have h1 : golombAux j <+: golombAux (max j m) := golombAux_prefix (le_max_left _ _)
  have h2 : golombAux m <+: golombAux (max j m) := golombAux_prefix (le_max_right _ _)
  have hj' : j < (golombAux j).length := by have := (golombAux_pos_length j).2; omega
  rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj, h1.getElem hj', h2.getElem hj]

theorem golombAux_eq_map (m : ℕ) :
    golombAux m = (List.range' 1 (golombAux m).length).map golomb := by
  apply List.ext_getElem (by simp)
  intro j h1 _
  rw [List.getElem_map, List.getElem_range', show 1 + 1 * j = j + 1 by ring, golomb_eq_getD h1,
    List.getD_eq_getElem _ _ h1]

theorem golombAux_succ' (m : ℕ) :
    golombAux (m + 1) = golombAux m ++ List.replicate (golomb (m + 3)) (m + 3) := by
  have h : m + 2 < (golombAux m).length := by have := (golombAux_pos_length m).2; omega
  rw [golombAux_succ, show m + 3 = m + 2 + 1 from rfl, golomb_eq_getD h]

/-- The self-describing property of Golomb's sequence: stage `m` of the construction lists
`1, 2, …, m + 2` in increasing order, each `k` repeated `golomb k` times. -/
theorem golombAux_eq_flatMap (m : ℕ) :
    golombAux m = (List.range' 1 (m + 2)).flatMap (fun k => List.replicate (golomb k) k) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [golombAux_succ', ih, show m + 1 + 2 = (m + 2) + 1 by omega,
      List.range'_concat (s := 1) (n := m + 2), List.flatMap_append, List.flatMap_singleton,
      show 1 + 1 * (m + 2) = m + 3 by omega]

/-- Row `1` of the triangle is `[1]`. -/
theorem row_one : row 1 = [1] := by decide

/-- The number of elements of row `n + 2` is the sum of row `n + 1`. -/
theorem length_row_succ_succ (n : ℕ) : (row (n + 2)).length = (row (n + 1)).sum := by
  show ((List.range' (rowEnd (n + 1) + 1) (rowEnd (n + 2) - rowEnd (n + 1))).map H).length =
    ((List.range' (rowEnd n + 1) (rowEnd (n + 1) - rowEnd n)).map H).sum
  rw [List.length_map, List.length_range']
  show rowEnd (n + 1) + _ - rowEnd (n + 1) = _
  omega

/-- The four rows shown in the entry (kernel-checked). -/
theorem rows_example :
    row 1 = [1] ∧ row 2 = [2] ∧ row 3 = [3, 3] ∧ row 4 = [4, 4, 4, 5, 5, 5] := by
  decide +kernel

theorem a_succ (n : ℕ) : a (n + 1) = rowEnd (n + 1) - rowEnd n := by
  simp [a, row]

theorem row_succ (n : ℕ) :
    row (n + 1) = (List.range' (rowEnd n + 1) (rowEnd (n + 1) - rowEnd n)).map H := by
  simp only [row, Nat.add_sub_cancel]

theorem levineRow_add_two (k : ℕ) : levineRow (k + 2) = levineAux (levineRow (k + 1)) 1 := rfl

/-! ### Fast evaluation (used only to check the data) -/

/-- Iterating `levineAux · 1` from `[1, 2, 2]` produces longer and longer prefixes of Golomb's
sequence (`golombFast_eq_golombAux`); `golombFast 5` has `6474` terms. -/
def golombFast : ℕ → List ℕ
  | 0 => [1, 2, 2]
  | i + 1 => levineAux (golombFast i) 1

theorem levineAux_map (f : ℕ → ℕ) (n i : ℕ) :
    levineAux ((List.range' i n).map f) i =
      (List.range' i n).flatMap (fun k => List.replicate (f k) k) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => rw [List.range'_succ, List.map_cons, levineAux, ih, List.flatMap_cons]

theorem levineAux_golombAux (m : ℕ) :
    levineAux (golombAux m) 1 = golombAux ((golombAux m).length - 2) := by
  have hlen := (golombAux_pos_length m).2
  rw [golombAux_eq_flatMap ((golombAux m).length - 2),
    show (golombAux m).length - 2 + 2 = (golombAux m).length by omega]
  conv_lhs => rw [golombAux_eq_map m]
  exact levineAux_map golomb _ 1

theorem golombFast_eq_golombAux (i : ℕ) : ∃ m, golombFast i = golombAux m := by
  induction i with
  | zero => exact ⟨0, rfl⟩
  | succ i ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨_, by show levineAux (golombFast i) 1 = _; rw [hm, levineAux_golombAux]⟩

/-- `H` read off a prefix of Golomb's sequence. -/
def hFast (i : ℕ) : List ℕ := 1 :: (golombFast i).drop 2

theorem H_eq_hFast (i j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (hFast i).length) :
    H j = (hFast i).getD (j - 1) 0 := by
  obtain ⟨m, hm⟩ := golombFast_eq_golombAux i
  have hlen := (golombAux_pos_length m).2
  rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj
  · rfl
  · have h2' : j < (golombAux m).length := by
      simp only [hFast, hm, List.length_cons, List.length_drop] at h2; omega
    rw [H, if_neg (by omega), golomb_eq_getD h2', hFast, hm,
      show j - 1 = (j - 2) + 1 by omega, List.getD_cons_succ, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_drop, show 2 + (j - 2) = j by omega]

theorem map_H_range' (i s c : ℕ) (h : s + c ≤ (hFast i).length) :
    (List.range' (s + 1) c).map H = ((hFast i).drop s).take c := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 _
    simp only [List.length_map, List.length_range'] at h1
    rw [List.getElem_map, List.getElem_range', List.getElem_take, List.getElem_drop,
      H_eq_hFast i (s + 1 + 1 * k) (by omega) (by omega), List.getD_eq_getElem _ _ (by omega)]
    congr 1; omega

/-- One step of the row recursion, on a list `hl` holding `H 1, H 2, …`:
`(rowEnd n, rowEnd (n + 1)) ↦ (rowEnd (n + 1), rowEnd (n + 2))`. -/
def rowStepL (hl : List ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.2, p.2 + ((hl.drop p.1).take (p.2 - p.1)).sum)

def rowPairL (hl : List ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => rowStepL hl (rowPairL hl n)

theorem rowPairL_fst_le_snd (hl : List ℕ) (n : ℕ) : (rowPairL hl n).1 ≤ (rowPairL hl n).2 := by
  cases n with
  | zero => show 0 ≤ 1; omega
  | succ n => show (rowPairL hl n).2 ≤ (rowPairL hl n).2 + _; omega

theorem rowPairL_fst_mono (hl : List ℕ) {n n' : ℕ} (h : n ≤ n') :
    (rowPairL hl n).1 ≤ (rowPairL hl n').1 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (rowPairL_fst_le_snd hl _)

theorem rowPairL_eq (i n : ℕ) (h : (rowPairL (hFast i) n).1 ≤ (hFast i).length) :
    rowPairL (hFast i) n = (rowEnd n, rowEnd (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hle := rowPairL_fst_le_snd (hFast i) n
    have h' : (rowPairL (hFast i) n).2 ≤ (hFast i).length := h
    have e := ih (by omega)
    rw [e] at hle h'
    dsimp only at hle h'
    show rowStepL (hFast i) (rowPairL (hFast i) n) = (rowEnd (n + 1), rowEnd (n + 2))
    rw [e]
    show (rowEnd (n + 1), rowEnd (n + 1) + _) = (rowEnd (n + 1), rowEnd (n + 1) +
      ((List.range' (rowEnd n + 1) (rowEnd (n + 1) - rowEnd n)).map H).sum)
    rw [map_H_range' i (rowEnd n) (rowEnd (n + 1) - rowEnd n) (by omega)]

theorem a_eq_fast {n : ℕ} (hn : n ≤ 7) :
    a (n + 1) = (rowPairL (hFast 5) n).2 - (rowPairL (hFast 5) n).1 := by
  have h7 : (rowPairL (hFast 5) 7).1 ≤ (hFast 5).length := by decide +kernel
  rw [a_succ, rowPairL_eq 5 n ((rowPairL_fst_mono _ hn).trans h7)]

theorem golomb_eq_fast (i j : ℕ) (hj : j < (golombFast i).length) :
    golomb (j + 1) = (golombFast i).getD j 0 := by
  obtain ⟨m, hm⟩ := golombFast_eq_golombAux i
  rw [hm] at hj ⊢
  exact golomb_eq_getD hj

theorem length_levineAux (l : List ℕ) (i : ℕ) : (levineAux l i).length = l.sum := by
  induction l generalizing i with
  | nil => rfl
  | cons c l ih => rw [levineAux, List.length_append, List.length_replicate, ih, List.sum_cons]

/-- The weighted sum `c₀ * i + c₁ * (i + 1) + ⋯ + c_r * (i + r)` of `[c₀, c₁, …, c_r]`. -/
def wsum : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: l, i => c * i + wsum l (i + 1)

theorem sum_levineAux (l : List ℕ) (i : ℕ) : (levineAux l i).sum = wsum l i := by
  induction l generalizing i with
  | nil => rfl
  | cons c l ih => rw [levineAux, List.sum_append, List.sum_replicate, ih, wsum, smul_eq_mul]

theorem map_H_range'_golomb (s c : ℕ) (hs : 2 ≤ s) :
    (List.range' s c).map H = (List.range' (s + 1) c).map golomb := by
  induction c generalizing s with
  | zero => rfl
  | succ c ih =>
    rw [List.range'_succ, List.range'_succ, List.map_cons, List.map_cons, ih (s + 1) (by omega)]
    simp only [H, if_neg (show ¬ s ≤ 1 by omega)]

/-- `a 9` needs `H` up to index `1090482`; it is the sum of `golomb j` over
`6475 ≤ j ≤ 1090483`, which is evaluated as a weighted sum of the first `6474` terms. -/
theorem a_nine : a 9 = 4362192095 := by
  have h7 := rowPairL_eq 5 7 (by decide +kernel)
  have hv : rowPairL (hFast 5) 7 = (6473, 1090482) := by decide +kernel
  rw [hv, Prod.mk.injEq] at h7
  obtain ⟨h7a, h8⟩ := h7
  have h5len : (golombFast 5).length = 6474 := by decide +kernel
  have h5sum : (golombFast 5).sum = 1090483 := by decide +kernel
  have h5w : wsum (golombFast 5) 1 = 1090483 + 4362192095 := by decide +kernel
  obtain ⟨m5, hm5⟩ := golombFast_eq_golombAux 5
  obtain ⟨m6, hm6⟩ := golombFast_eq_golombAux 6
  have h6len : (golombFast 6).length = 1090483 := by
    show (levineAux (golombFast 5) 1).length = _
    rw [length_levineAux, h5sum]
  have h6sum : (golombFast 6).sum = 1090483 + 4362192095 := by
    show (levineAux (golombFast 5) 1).sum = _
    rw [sum_levineAux, h5w]
  have e5 : golombFast 5 = (List.range' 1 6474).map golomb := by
    rw [← h5len, hm5]
    exact golombAux_eq_map m5
  have hsplit : List.range' 1 1090483 = List.range' 1 6474 ++ List.range' 6475 1084009 :=
    (List.range'_append (s := 1) (m := 6474) (n := 1084009) (step := 1)).symm
  have e6 : golombFast 6 = (List.range' 1 6474 ++ List.range' 6475 1084009).map golomb := by
    rw [← hsplit, ← h6len, hm6]
    exact golombAux_eq_map m6
  have key : (golombFast 6).sum =
      (golombFast 5).sum + ((List.range' 6475 1084009).map golomb).sum := by
    rw [e6, List.map_append, List.sum_append, ← e5]
  have e9 :
      a (7 + 2) = ((List.range' (rowEnd 7 + 1) (rowEnd (7 + 1) - rowEnd 7)).map H).sum := by
    rw [a, length_row_succ_succ, row_succ]
  rw [show (9 : ℕ) = 7 + 2 from rfl, e9, ← h7a, ← h8,
    show (6473 + 1 : ℕ) = 6474 from rfl, show (1090482 - 6473 : ℕ) = 1084009 from rfl,
    map_H_range'_golomb 6474 1084009 (by norm_num), show (6474 + 1 : ℕ) = 6475 from rfl]
  omega

/-! ### Data checks -/

/-- The definition of Golomb's sequence reproduces all 84 terms listed in A001462
(kernel-checked). -/
theorem golomb_data : (List.range 84).map (fun i => golomb (i + 1)) =
    [1, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10,
      10, 10, 10, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 14, 14, 14,
      14, 14, 14, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17,
      18, 18, 18, 18, 18, 18, 18, 19] := by
  have h : (golombFast 4).length = 272 := by decide +kernel
  rw [List.map_congr_left (fun i hi => golomb_eq_fast 4 i (by
    have := List.mem_range.1 hi; omega))]
  decide +kernel

theorem row_eq_fast {n : ℕ} (hn : n ≤ 6) :
    row (n + 1) = ((hFast 5).drop (rowPairL (hFast 5) n).1).take
      ((rowPairL (hFast 5) n).2 - (rowPairL (hFast 5) n).1) := by
  have h7 : (rowPairL (hFast 5) 7).1 ≤ (hFast 5).length := by decide +kernel
  have e := rowPairL_eq 5 n ((rowPairL_fst_mono _ (by omega : n ≤ 7)).trans h7)
  have hb := (rowPairL_fst_mono (hFast 5) (by omega : n + 1 ≤ 7)).trans h7
  have hle := rowPairL_fst_le_snd (hFast 5) n
  rw [e] at hle ⊢
  rw [rowPairL_eq 5 (n + 1) hb] at hb
  dsimp only at hle hb ⊢
  rw [row_succ, map_H_range' 5 _ _ (by omega)]

/-- The last elements of rows `1, …, 7` of the triangle (kernel-checked). -/
theorem rowLast_data : (List.range 7).map (fun i => (row (i + 1)).getLast?) =
    [some 1, some 2, some 3, some 5, some 11, some 38, some 272] := by
  rw [List.map_congr_left (fun i hi => congrArg List.getLast?
    (row_eq_fast (by have := List.mem_range.1 hi; omega)))]
  decide +kernel

/-- The definition reproduces all 9 terms listed in OEIS, `a 1, …, a 9` (kernel-checked). -/
theorem a_data : (List.range 9).map (fun i => a (i + 1)) =
    [1, 1, 2, 6, 27, 234, 6202, 1084009, 4362192095] := by
  rw [show List.range 9 = List.range 8 ++ [8] by decide, List.map_append, List.map_singleton,
    show a (8 + 1) = 4362192095 from a_nine,
    List.map_congr_left (fun i hi => a_eq_fast (by have := List.mem_range.1 hi; omega))]
  decide +kernel

theorem levineAux_pos (l : List ℕ) (i : ℕ) : ∀ x ∈ levineAux l i, i ≤ x := by
  induction l generalizing i with
  | nil => intro x hx; simp [levineAux] at hx
  | cons c l ih =>
    intro x hx
    rw [levineAux, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]
    · have := ih (i + 1) x hx; omega

theorem levineRow_pos (k : ℕ) : ∀ x ∈ levineRow k, 1 ≤ x := by
  match k with
  | 0 => intro x hx; simp [levineRow] at hx
  | 1 => decide
  | k + 2 => exact levineAux_pos _ 1

theorem getLast?_levineAux : ∀ (l : List ℕ) (i : ℕ), l ≠ [] → (∀ x ∈ l, 1 ≤ x) →
    (levineAux l i).getLast? = some (i + l.length - 1)
  | [], _, h, _ => absurd rfl h
  | [c], i, _, hpos => by
    have hc : 1 ≤ c := hpos c (List.mem_singleton_self c)
    rw [levineAux, levineAux, List.append_nil, List.getLast?_replicate, if_neg (by omega)]
    simp
  | c :: d :: l, i, _, hpos => by
    rw [levineAux, List.getLast?_append, getLast?_levineAux (d :: l) (i + 1)
      (List.cons_ne_nil _ _) (fun x hx => hpos x (List.mem_cons_of_mem _ hx))]
    simp only [Option.some_or, List.length_cons]
    congr 1
    omega

/-- The final term of row `k + 2` of Levine's array is the length of row `k + 1`. -/
theorem A014644_add_two (k : ℕ) (hne : levineRow (k + 1) ≠ []) :
    A014644 (k + 2) = (levineRow (k + 1)).length := by
  rw [A014644, levineRow_add_two, List.getLastD_eq_getLast?,
    getLast?_levineAux _ _ hne (levineRow_pos _)]
  simp

/-- Levine's sequence: the definition reproduces the first 11 terms listed in A014644
(kernel-checked; terms `9`–`11` via `A014644_add_two`, `length_levineAux` and
`sum_levineAux`, since rows `9` and `10` have `1090483` and `4363282578` terms). -/
theorem A014644_data : (List.range 11).map (fun i => A014644 (i + 1)) =
    [1, 2, 2, 3, 5, 11, 38, 272, 6474, 1090483, 4363282578] := by
  have h8 : (levineRow (7 + 1)).length = 6474 ∧ (levineRow (7 + 1)).sum = 1090483 ∧
      wsum (levineRow (7 + 1)) 1 = 4363282578 := by decide +kernel
  have l9 : (levineRow (8 + 1)).length = 1090483 := by
    rw [levineRow_add_two, length_levineAux, h8.2.1]
  have s9 : (levineRow (8 + 1)).sum = 4363282578 := by
    rw [levineRow_add_two, sum_levineAux, h8.2.2]
  have l10 : (levineRow (9 + 1)).length = 4363282578 := by
    rw [levineRow_add_two, length_levineAux, s9]
  have h9 : A014644 (8 + 1) = 6474 := by
    rw [A014644_add_two 7 (List.ne_nil_of_length_pos (by rw [h8.1]; norm_num)), h8.1]
  have h10 : A014644 (9 + 1) = 1090483 := by
    rw [A014644_add_two 8 (List.ne_nil_of_length_pos (by rw [l9]; norm_num)), l9]
  have h11 : A014644 (10 + 1) = 4363282578 := by
    rw [A014644_add_two 9 (List.ne_nil_of_length_pos (by rw [l10]; norm_num)), l10]
  rw [show List.range 11 = List.range 8 ++ [8, 9, 10] by decide, List.map_append,
    List.map_cons, List.map_cons, List.map_singleton, h9, h10, h11]
  decide +kernel

/-! ### The conjecture -/

/-- Conjectures (Floor van Lamoen and Paul D. Hanna, 2005):
(1) for every `n ≥ 2`, `a n = A014644 (n + 2) - A014644 (n + 1)`, i.e. the terms `a 2, a 3, …`
are the first differences of A014644 taken from its third term on;
(2) the final elements of rows `1, 2, 3, …` of the triangle are A014644 with the duplicate `2`
(`A014644 2 = A014644 3 = 2`) removed: the last element of row `1` is `A014644 1`, and the last
element of row `n` is `A014644 (n + 1)` for every `n ≥ 2`. -/
def statement : Prop :=
  (∀ n : ℕ, 2 ≤ n → (a n : ℤ) = (A014644 (n + 2) : ℤ) - (A014644 (n + 1) : ℤ)) ∧
  ((row 1).getLast? = some (A014644 1) ∧
    ∀ n : ℕ, 2 ≤ n → (row n).getLast? = some (A014644 (n + 1)))

end Math0.Statements.A113676
