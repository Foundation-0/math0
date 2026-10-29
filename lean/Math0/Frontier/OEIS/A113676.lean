/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A113676
import Math0.Audit

/-!
# The Golomb-row triangle A113676 and Levine's sequence A014644

We prove both conjectures of Floor van Lamoen and Paul D. Hanna (2005).

Write `G = golomb`, `P(l) = [G 1, …, G l]` and `L k = (levineRow k).length`.

**Levine's rows are prefixes of Golomb's sequence.** Applying Levine's map `levineAux · 1` to
`P(l)` (`l ≥ 2`) gives `1^G(1) 2^G(2) ⋯ l^G(l)`, which is a stage of the self-generating
construction of Golomb's sequence, hence again a prefix `P(l')`. Since `levineRow 2 = [1, 2]`,
induction gives `levineRow k = P(L k)` for all `k ≥ 2`. Moreover `L (k + 1) = sum (levineRow k)`,
so `L k ≤ L (k + 1)`; the final term of `levineRow (k + 1)` is
`A014644 (k + 1) = G (L (k + 1))`, and also `A014644 (k + 2) = L (k + 1)`.

**Telescoping.** Splitting `P(L (k + 1)) = P(L k) ++ [G (L k + 1), …, G (L (k + 1))]` and taking
sums gives `G (L k + 1) + ⋯ + G (L (k + 1)) = L (k + 2) - L (k + 1)` for `k ≥ 2`.

**The rows.** Since `H j = G (j + 1)` for `j ≥ 2`, the row recursion and the telescoping identity
give by induction `rowEnd n + 1 = L (n + 1)` for all `n ≥ 1`. Hence for `n ≥ 2`, row `n` is
`[G (L n + 1), …, G (L (n + 1))]`, its length is
`L (n + 1) - L n = A014644 (n + 2) - A014644 (n + 1)`, and (as `L n < L (n + 1)`, by induction
on the differences) its last term is `G (L (n + 1)) = A014644 (n + 1)`.
-/

namespace Math0.Frontier.A113676
open Math0.Statements.A113676

/-- Golomb's sequence is positive from index `1` on. -/
private lemma golomb_pos {i : ℕ} (hi : 1 ≤ i) : 1 ≤ golomb i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hlen := (golombAux_pos_length j).2
  rw [golomb_eq_getD (m := j) (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact (golombAux_pos_length j).1 _ (List.getElem_mem _)

/-- A block of `c` consecutive Golomb terms (from index `s + 1` on) has sum at least `c`. -/
private lemma le_sum_map_golomb (s c : ℕ) : c ≤ ((List.range' (s + 1) c).map golomb).sum := by
  have h := List.length_le_sum_of_one_le ((List.range' (s + 1) c).map golomb) (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range'_1] at hi
    exact golomb_pos (by omega))
  simpa using h

/-- The rows of Levine's array (from row `1` on) have at least two terms. -/
private lemma two_le_length_levineRow (k : ℕ) (hk : 1 ≤ k) : 2 ≤ (levineRow k).length := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [levineRow_add_two, length_levineAux]
    exact ih.trans (List.length_le_sum_of_one_le _ (levineRow_pos _))

/-- The length of row `k + 1` of Levine's array is the sum of row `k` (`k ≥ 1`). -/
private lemma length_levineRow_succ (k : ℕ) (hk : 1 ≤ k) :
    (levineRow (k + 1)).length = (levineRow k).sum := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [levineRow_add_two, length_levineAux]

/-- Row lengths of Levine's array are nondecreasing (from row `1` on). -/
private lemma length_levineRow_le (k : ℕ) (hk : 1 ≤ k) :
    (levineRow k).length ≤ (levineRow (k + 1)).length := by
  rw [length_levineRow_succ k hk]
  exact List.length_le_sum_of_one_le _ (levineRow_pos _)

/-- Rows `k ≥ 2` of Levine's array are prefixes of Golomb's sequence. -/
private lemma levineRow_eq (k : ℕ) (hk : 2 ≤ k) :
    levineRow k = (List.range' 1 (levineRow k).length).map golomb := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h2 := two_le_length_levineRow (j + 1) (by omega)
    have e : levineRow (j + 1 + 1) = golombAux ((levineRow (j + 1)).length - 2) := by
      have hm := levineAux_map golomb (levineRow (j + 1)).length 1
      rw [← ih] at hm
      rw [levineRow_add_two, hm, golombAux_eq_flatMap, Nat.sub_add_cancel h2]
    rw [e]
    exact golombAux_eq_map _

/-- Telescoping: for `k ≥ 2`, the Golomb terms of indices `L k + 1, …, L (k + 1)` sum to
`L (k + 2) - L (k + 1)`, where `L k = (levineRow k).length`. -/
private lemma sum_block (k : ℕ) (hk : 2 ≤ k) :
    (levineRow (k + 1)).length +
      ((List.range' ((levineRow k).length + 1)
        ((levineRow (k + 1)).length - (levineRow k).length)).map golomb).sum =
      (levineRow (k + 2)).length := by
  have hle := length_levineRow_le k (by omega)
  have hsplit : List.range' 1 (levineRow (k + 1)).length =
      List.range' 1 (levineRow k).length ++
        List.range' ((levineRow k).length + 1)
          ((levineRow (k + 1)).length - (levineRow k).length) := by
    rw [show (levineRow k).length + 1 = 1 + (levineRow k).length by omega,
      List.range'_append_1, Nat.add_sub_cancel' hle]
  have e1 := levineRow_eq (k + 1) (by omega)
  rw [hsplit, List.map_append, ← levineRow_eq k hk] at e1
  have s3 := congrArg List.sum e1
  rw [List.sum_append] at s3
  have s1 : (levineRow (k + 2)).length = (levineRow (k + 1)).sum :=
    length_levineRow_succ (k + 1) (by omega)
  have s2 : (levineRow (k + 1)).length = (levineRow k).sum := length_levineRow_succ k (by omega)
  omega

/-- The row ends of the triangle: `rowEnd n + 1 = L (n + 1)` for `n ≥ 1`. -/
private lemma rowEnd_eq (n : ℕ) (hn : 1 ≤ n) :
    rowEnd n + 1 = (levineRow (n + 1)).length ∧
      rowEnd (n + 1) + 1 = (levineRow (n + 2)).length := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨ih2, ?_⟩
    have h2 : 2 ≤ (levineRow (n + 1)).length := two_le_length_levineRow (n + 1) (by omega)
    have hb : (levineRow (n + 2)).length +
        ((List.range' ((levineRow (n + 1)).length + 1)
          ((levineRow (n + 2)).length - (levineRow (n + 1)).length)).map golomb).sum =
        (levineRow (n + 3)).length := sum_block (n + 1) (by omega)
    have e : rowEnd (n + 2) = rowEnd (n + 1) +
        ((List.range' (rowEnd n + 1) (rowEnd (n + 1) - rowEnd n)).map H).sum := rfl
    show rowEnd (n + 2) + 1 = (levineRow (n + 3)).length
    rw [e, map_H_range'_golomb _ _ (by omega),
      show rowEnd n + 1 + 1 = (levineRow (n + 1)).length + 1 by omega,
      show rowEnd (n + 1) - rowEnd n =
        (levineRow (n + 2)).length - (levineRow (n + 1)).length by omega]
    omega

/-- Levine's row lengths are strictly increasing from row `2` on. -/
private lemma length_levineRow_lt (k : ℕ) (hk : 1 ≤ k) :
    (levineRow (k + 1)).length < (levineRow (k + 2)).length := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hb : (levineRow (k + 2)).length +
        ((List.range' ((levineRow (k + 1)).length + 1)
          ((levineRow (k + 2)).length - (levineRow (k + 1)).length)).map golomb).sum =
        (levineRow (k + 3)).length := sum_block (k + 1) (by omega)
    have hs := le_sum_map_golomb (levineRow (k + 1)).length
      ((levineRow (k + 2)).length - (levineRow (k + 1)).length)
    show (levineRow (k + 2)).length < (levineRow (k + 3)).length
    omega

/-- The last term of `map f (range' s (c + 1))`. -/
private lemma getLast?_map_range' (f : ℕ → ℕ) (s c : ℕ) :
    ((List.range' s (c + 1)).map f).getLast? = some (f (s + c)) := by
  rw [List.range'_1_concat, List.map_append, List.getLast?_append]
  simp

/-- Both conjectures of van Lamoen and Hanna hold: the row lengths `a n` (`n ≥ 2`) are the first
differences of Levine's sequence A014644 from its third term on, and the final elements of the
rows are A014644 with its duplicate `2` removed. -/
theorem result : statement := by
  -- Row `m + 2` is the block of Golomb terms of indices `L (m + 2) + 1, …, L (m + 3)`.
  have hrow : ∀ m : ℕ, row (m + 2) = (List.range' ((levineRow (m + 2)).length + 1)
      ((levineRow (m + 3)).length - (levineRow (m + 2)).length)).map golomb := by
    intro m
    have h0 : 2 ≤ (levineRow (m + 2)).length := two_le_length_levineRow (m + 2) (by omega)
    have h1 : rowEnd (m + 1) + 1 = (levineRow (m + 2)).length := (rowEnd_eq (m + 1) (by omega)).1
    have h2 : rowEnd (m + 1 + 1) + 1 = (levineRow (m + 3)).length :=
      (rowEnd_eq (m + 1) (by omega)).2
    show row (m + 1 + 1) = _
    rw [row_succ, map_H_range'_golomb _ _ (by omega),
      show rowEnd (m + 1) + 1 + 1 = (levineRow (m + 2)).length + 1 by omega,
      show rowEnd (m + 1 + 1) - rowEnd (m + 1) =
        (levineRow (m + 3)).length - (levineRow (m + 2)).length by omega]
  have hA : ∀ k : ℕ, 1 ≤ k → A014644 (k + 1) = (levineRow k).length := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact A014644_add_two j (List.ne_nil_of_length_pos
      (by have := two_le_length_levineRow (j + 1) (by omega); omega))
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hlt : (levineRow (m + 2)).length < (levineRow (m + 3)).length :=
      length_levineRow_lt (m + 1) (by omega)
    have hA3 : A014644 (m + 2 + 2) = (levineRow (m + 3)).length := hA (m + 3) (by omega)
    have hA2 : A014644 (m + 2 + 1) = (levineRow (m + 2)).length := hA (m + 2) (by omega)
    rw [a, hrow m, List.length_map, List.length_range', hA3, hA2]
    push_cast [hlt.le]
    ring
  · rw [row_one]
    rfl
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hlt : (levineRow (m + 2)).length < (levineRow (m + 3)).length :=
      length_levineRow_lt (m + 1) (by omega)
    have hlast : A014644 (m + 2 + 1) = golomb (levineRow (m + 3)).length := by
      have e := levineRow_eq (m + 3) (by omega)
      obtain ⟨d, hd⟩ : ∃ d, (levineRow (m + 3)).length = d + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      rw [hd] at e
      show (levineRow (m + 3)).getLastD 0 = _
      rw [List.getLastD_eq_getLast?, hd, e, getLast?_map_range', Option.getD_some,
        Nat.add_comm]
    obtain ⟨c, hc⟩ : ∃ c, (levineRow (m + 3)).length - (levineRow (m + 2)).length = c + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    rw [hrow m, hc, getLast?_map_range', hlast]
    congr 2
    omega

end Math0.Frontier.A113676

#math0_settles Math0.Frontier.A113676.result Math0.Statements.A113676.statement
