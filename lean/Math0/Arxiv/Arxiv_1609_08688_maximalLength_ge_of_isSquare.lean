/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Arxiv.«1609.08688».sIncreasingrTuples
import Math0.Audit

/-!
# A 2-increasing sequence of length `n ^ (3/2)` (Gowers–Long)

Let `F(n)` be the maximal length of a sequence of triples in `[1, n]^3` in which every earlier
triple is smaller than every later one in at least two coordinates. Gowers and Long
[arXiv:1609.08688, Proposition 1.4] observe that `F(n) ≥ n ^ (3/2)` when `n` is a perfect square.
We prove exactly the formal statement `Arxiv.«1609.08688».maximalLength_ge_of_isSquare`:
if `n = k * k` then `k ^ 3 ≤ F(n)`. The witness lists, for `(a, b, c) ∈ [0, k)^3` in
lexicographic order, the triple `(a k + b + 1, a k + c + 1, b k + c + 1)`, i.e. the pairs
`((a, b), (a, c), (b, c))` written in base `k`. When the first index that changes is `a`, `b`
or `c`, the coordinates `{1, 2}`, `{1, 3}` or `{2, 3}` respectively increase. Boundedness of the
set of lengths (needed for `le_csSup`) comes from the pigeonhole bound `n ^ 2`.
-/

open Arxiv.«1609.08688»

namespace Math0.Arxiv.«1609.08688»

/-- The triple `((a,b),(a,c),(b,c))` with pairs encoded in base `k`, shifted to start at `1`. -/
def triple (k a b c : ℕ) : Fin 3 → ℕ := ![a * k + b + 1, a * k + c + 1, b * k + c + 1]

/-- The sequence of all triples `triple k a b c` for `a, b, c < k`, in lexicographic order. -/
def seq (k : ℕ) : List (Fin 3 → ℕ) :=
  (List.range k).flatMap fun a => (List.range k).flatMap fun b =>
    (List.range k).map fun c => triple k a b c

/-- The sequence has length `k ^ 3`. -/
lemma length_seq (k : ℕ) : (seq k).length = k ^ 3 := by
  simp [seq, List.length_flatMap]
  ring

/-- Changing `a` to a larger value increases the first two coordinates. -/
lemma lt₂_of_lt_a {k a b c a' b' c' : ℕ} (ha : a < a') (hb : b < k) (hc : c < k) :
    lt₂ (triple k a b c) (triple k a' b' c') := by
  have h : (a + 1) * k ≤ a' * k := Nat.mul_le_mul_right _ ha
  refine ⟨0, 1, by decide, ?_, ?_⟩ <;> simp [triple] <;> nlinarith

/-- Keeping `a` and increasing `b` increases the first and third coordinates. -/
lemma lt₂_of_lt_b {k a b c b' c' : ℕ} (hb : b < b') (hc : c < k) :
    lt₂ (triple k a b c) (triple k a b' c') := by
  have h : (b + 1) * k ≤ b' * k := Nat.mul_le_mul_right _ hb
  refine ⟨0, 2, by decide, ?_, ?_⟩ <;> simp [triple] <;> nlinarith

/-- Keeping `a, b` and increasing `c` increases the second and third coordinates. -/
lemma lt₂_of_lt_c {k a b c c' : ℕ} (hc : c < c') :
    lt₂ (triple k a b c) (triple k a b c') := by
  refine ⟨1, 2, by decide, ?_, ?_⟩ <;> simp [triple] <;> omega

/-- The sequence `seq k` is `2`-increasing. -/
lemma isIncreasing₂_seq (k : ℕ) : IsIncreasing₂ (seq k) := by
  unfold IsIncreasing₂ seq
  simp only [List.pairwise_flatMap, List.pairwise_map, List.mem_range, List.mem_flatMap,
    List.mem_map]
  refine ⟨fun a _ => ⟨fun b _ => ?_, ?_⟩, ?_⟩
  · exact List.pairwise_lt_range.imp fun h => lt₂_of_lt_c h
  · refine List.pairwise_lt_range.imp_of_mem fun _ _ h => ?_
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', -, rfl⟩
    exact lt₂_of_lt_b h hc
  · refine List.pairwise_lt_range.imp_of_mem fun _ _ h => ?_
    rintro _ ⟨b, hb, c, hc, rfl⟩ _ ⟨b', -, c', -, rfl⟩
    exact lt₂_of_lt_a h hb hc

/-- All coordinates of all triples of `seq k` lie in `[1, k * k]`. -/
lemma range_seq (k : ℕ) : ∀ t ∈ seq k, Set.range t ⊆ Set.Icc 1 (k * k) := by
  intro t ht
  simp only [seq, List.mem_flatMap, List.mem_range, List.mem_map] at ht
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := ht
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [triple] <;> nlinarith

/-- For `n ≥ 2`, every `2`-increasing sequence of triples in `[1, n]` has length at most
`F(n)` (the set of lengths is bounded above by `n ^ 2` by pigeonhole). -/
lemma length_le_maximalLength {n : ℕ} (hn : 2 ≤ n) {s : List (Fin 3 → ℕ)}
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs₂ : IsIncreasing₂ s) :
    s.length ≤ maximalLength n := by
  rw [maximalLength]
  refine le_csSup ⟨n ^ 2, ?_⟩ ⟨s, hs₁, hs₂, rfl⟩
  rintro _ ⟨t, ht₁, ht₂, rfl⟩
  by_contra hle
  obtain ⟨i, j, hij, h0, h1⟩ := exists_pair_of_mem_Icc hn ht₁ (Nat.lt_of_not_ge hle)
  have hp : t.Pairwise lt₂ := ht₂
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.ge h1.ge) (List.pairwise_iff_get.1 hp i j hij)
  · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.le h1.le) (List.pairwise_iff_get.1 hp j i hji)

/-- If `n` is a perfect square then `F(n) ≥ (√n) ^ 3`. -/
theorem maximalLength_ge_of_isSquare :
    type_of% @Arxiv.«1609.08688».maximalLength_ge_of_isSquare := by
  rintro n ⟨k, rfl⟩
  rw [Nat.sqrt_eq]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp
    · simp [maximalLength_one]
  · rw [← length_seq k]
    exact length_le_maximalLength (by nlinarith) (range_seq k) (isIncreasing₂_seq k)

end Math0.Arxiv.«1609.08688»

#math0_proves Math0.Arxiv.«1609.08688».maximalLength_ge_of_isSquare Arxiv.«1609.08688».maximalLength_ge_of_isSquare
