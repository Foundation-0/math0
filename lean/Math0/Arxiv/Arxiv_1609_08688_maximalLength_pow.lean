/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Arxiv.«1609.08688».sIncreasingrTuples
import Math0.Audit

/-!
# Powers of `F(n)` propagate to arbitrarily large `m` (Gowers–Long)

Let `F(n)` be the maximal length of a sequence of triples in `[1, n]^3` in which every earlier
triple is smaller than every later one in at least two coordinates. Gowers and Long
[arXiv:1609.08688] note that if `F(n) = n ^ α` for some `n > 1`, then `F(m) ≥ m ^ α` for
arbitrarily large `m`. We prove exactly the formal statement
`Arxiv.«1609.08688».maximalLength_pow`. The key step is supermultiplicativity
`F(a) F(b) ≤ F(a b)`: given optimal sequences `s` (in `[1, a]`) and `t` (in `[1, b]`), the
sequence of triples `b (x - 1) + y` for `x ∈ s`, `y ∈ t`, listed lexicographically in `(x, y)`,
is `2`-increasing with coordinates in `[1, a b]`. Induction gives `F(n) ^ j ≤ F(n ^ j)`, and
`(n ^ j) ^ α = (n ^ α) ^ j = F(n) ^ j`, so `m = n ^ j` works for every `j`.
-/

open Arxiv.«1609.08688»

namespace Math0.Arxiv.«1609.08688»

namespace MaximalLengthPow

/-- Every `2`-increasing sequence of triples in `[1, n]` has length at most `(n + 2) ^ 2`
(pigeonhole on the first two coordinates, applied in the larger box `[1, n + 2]`). -/
lemma length_le_sq {n : ℕ} {s : List (Fin 3 → ℕ)}
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs₂ : IsIncreasing₂ s) :
    s.length ≤ (n + 2) ^ 2 := by
  have hs₁' : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 (n + 2) := fun a ha =>
    (hs₁ a ha).trans (Set.Icc_subset_Icc le_rfl (by omega))
  by_contra hle
  obtain ⟨i, j, hij, h0, h1⟩ := exists_pair_of_mem_Icc (by omega) hs₁' (Nat.lt_of_not_ge hle)
  have hp : s.Pairwise lt₂ := hs₂
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.ge h1.ge) (List.pairwise_iff_get.1 hp i j hij)
  · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.le h1.le) (List.pairwise_iff_get.1 hp j i hji)

/-- The set of lengths whose supremum defines `F(n)` is bounded above. -/
lemma bddAbove_lengths (n : ℕ) :
    BddAbove { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n)
      (_ : IsIncreasing₂ s) } := by
  refine ⟨(n + 2) ^ 2, ?_⟩
  rintro _ ⟨s, hs₁, hs₂, rfl⟩
  exact length_le_sq hs₁ hs₂

/-- Every `2`-increasing sequence of triples in `[1, n]` has length at most `F(n)`. -/
lemma length_le_F {n : ℕ} {s : List (Fin 3 → ℕ)}
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs₂ : IsIncreasing₂ s) :
    s.length ≤ maximalLength n :=
  le_csSup (bddAbove_lengths n) ⟨s, hs₁, hs₂, rfl⟩

/-- The supremum `F(n)` is attained by some `2`-increasing sequence. -/
lemma exists_length_eq_F (n : ℕ) : ∃ s : List (Fin 3 → ℕ),
    (∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) ∧ IsIncreasing₂ s ∧ s.length = maximalLength n := by
  have hmem : maximalLength n ∈ { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n)
      (_ : IsIncreasing₂ s) } :=
    Nat.sSup_mem ⟨0, ⟨[], by simp, isIncreasing₂_nil, rfl⟩⟩ (bddAbove_lengths n)
  obtain ⟨s, hs₁, hs₂, h⟩ := hmem
  exact ⟨s, hs₁, hs₂, h⟩

/-- The combined triple with coordinates `b (x_i - 1) + y_i`. -/
def comb (b : ℕ) (x y : Fin 3 → ℕ) : Fin 3 → ℕ := fun i => b * (x i - 1) + y i

/-- The product sequence: all `comb b x y` with `x ∈ s`, `y ∈ t`, lexicographically. -/
def prodSeq (b : ℕ) (s t : List (Fin 3 → ℕ)) : List (Fin 3 → ℕ) :=
  s.flatMap fun x => t.map (comb b x)

/-- The product sequence has length `|s| |t|`. -/
lemma length_prodSeq (b : ℕ) (s t : List (Fin 3 → ℕ)) :
    (prodSeq b s t).length = s.length * t.length := by
  simp [prodSeq, List.length_flatMap]

/-- Coordinates of the product sequence lie in `[1, a b]`. -/
lemma range_prodSeq {a b : ℕ} {s t : List (Fin 3 → ℕ)}
    (hs : ∀ x ∈ s, Set.range x ⊆ Set.Icc 1 a) (ht : ∀ y ∈ t, Set.range y ⊆ Set.Icc 1 b) :
    ∀ z ∈ prodSeq b s t, Set.range z ⊆ Set.Icc 1 (a * b) := by
  intro z hz
  simp only [prodSeq, List.mem_flatMap, List.mem_map] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  rintro _ ⟨i, rfl⟩
  have hxi := hs x hx ⟨i, rfl⟩
  have hyi := ht y hy ⟨i, rfl⟩
  simp only [Set.mem_Icc] at hxi hyi ⊢
  obtain ⟨u, hu⟩ : ∃ u, x i = u + 1 := ⟨x i - 1, by omega⟩
  have h1 : b * (u + 1) ≤ b * a := Nat.mul_le_mul_left b (by omega)
  simp only [comb, hu, Nat.add_sub_cancel]
  constructor
  · omega
  · rw [mul_comm a b]; nlinarith

/-- Within a block (fixed `x`), the order of `t` is preserved. -/
lemma lt₂_comb_right {b : ℕ} {x y y' : Fin 3 → ℕ} (h : lt₂ y y') :
    lt₂ (comb b x y) (comb b x y') := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  exact ⟨i, j, hij, by simp only [comb]; omega, by simp only [comb]; omega⟩

/-- Between blocks, `x <₂ x'` forces `comb b x y <₂ comb b x' y'`. -/
lemma lt₂_comb_left {a b : ℕ} {x x' y y' : Fin 3 → ℕ}
    (hx : Set.range x ⊆ Set.Icc 1 a) (hy : Set.range y ⊆ Set.Icc 1 b)
    (hy' : Set.range y' ⊆ Set.Icc 1 b) (h : lt₂ x x') :
    lt₂ (comb b x y) (comb b x' y') := by
  have key : ∀ k, x k < x' k → comb b x y k < comb b x' y' k := by
    intro k hk
    have hxk := hx ⟨k, rfl⟩
    have hyk := hy ⟨k, rfl⟩
    have hyk' := hy' ⟨k, rfl⟩
    simp only [Set.mem_Icc] at hxk hyk hyk'
    have h1 : b * ((x k - 1) + 1) ≤ b * (x' k - 1) := Nat.mul_le_mul_left b (by omega)
    simp only [comb]
    rw [mul_add, mul_one] at h1
    omega
  obtain ⟨i, j, hij, hi, hj⟩ := h
  exact ⟨i, j, hij, key i hi, key j hj⟩

/-- The product of two `2`-increasing sequences is `2`-increasing. -/
lemma isIncreasing₂_prodSeq {a b : ℕ} {s t : List (Fin 3 → ℕ)}
    (hs : ∀ x ∈ s, Set.range x ⊆ Set.Icc 1 a) (ht : ∀ y ∈ t, Set.range y ⊆ Set.Icc 1 b)
    (hs₂ : IsIncreasing₂ s) (ht₂ : IsIncreasing₂ t) :
    IsIncreasing₂ (prodSeq b s t) := by
  unfold IsIncreasing₂ prodSeq at *
  rw [List.pairwise_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact ht₂.imp lt₂_comb_right
  · refine hs₂.imp_of_mem fun {x x'} hx _ h => ?_
    intro z hz z' hz'
    simp only [List.mem_map] at hz hz'
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨y', hy', rfl⟩ := hz'
    exact lt₂_comb_left (hs x hx) (ht y hy) (ht y' hy') h

/-- Supermultiplicativity: `F(a) F(b) ≤ F(a b)`. -/
lemma F_mul_le (a b : ℕ) : maximalLength a * maximalLength b ≤ maximalLength (a * b) := by
  obtain ⟨s, hs₁, hs₂, hs⟩ := exists_length_eq_F a
  obtain ⟨t, ht₁, ht₂, ht⟩ := exists_length_eq_F b
  rw [← hs, ← ht, ← length_prodSeq b s t]
  exact length_le_F (range_prodSeq hs₁ ht₁) (isIncreasing₂_prodSeq hs₁ ht₁ hs₂ ht₂)

/-- `F(n) ^ j ≤ F(n ^ j)`. -/
lemma F_pow_le (n j : ℕ) : maximalLength n ^ j ≤ maximalLength (n ^ j) := by
  induction j with
  | zero => simp [maximalLength_one]
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact (Nat.mul_le_mul_right _ ih).trans (F_mul_le _ _)

end MaximalLengthPow

open MaximalLengthPow in
/-- If `F(n) = n ^ e` for some `n > 1`, then `m ^ e ≤ F(m)` for arbitrarily large `m`
(namely for every power `m = n ^ j`). -/
theorem maximalLength_pow : type_of% @Arxiv.«1609.08688».maximalLength_pow := by
  intro n e hn h
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨n ^ N, (Nat.lt_pow_self hn).le, ?_⟩
  have h1 : ((n ^ N : ℕ) : ℝ) ^ e = (maximalLength n : ℝ) ^ N := by
    rw [h, Nat.cast_pow, Real.rpow_pow_comm (Nat.cast_nonneg n)]
  rw [h1]
  exact_mod_cast F_pow_le n N

end Math0.Arxiv.«1609.08688»

#math0_proves Math0.Arxiv.«1609.08688».maximalLength_pow Arxiv.«1609.08688».maximalLength_pow
