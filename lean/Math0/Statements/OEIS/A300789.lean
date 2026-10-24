/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A300789: Heinz numbers of domino-tileable Young diagrams

Source: https://oeis.org/A300789, _Gus Wiseman_, Mar 12 2018. Verbatim (COMMENTS):
> This sequence is conjectured to be the Heinz numbers of integer partitions in which the odd
> parts appear as many times in even as in odd positions.

The entry's name is "Heinz numbers of integer partitions whose Young diagram can be tiled by
dominos." (offset `1`), with the comment "The Heinz number of an integer partition
(y_1,...,y_k) is prime(y_1)*...*prime(y_k)."

## Encoding

* *Partitions and Heinz numbers.* Every `k ≥ 1` is the Heinz number of exactly one integer
  partition: its parts are the prime indices of `k`, i.e. `i` once for each prime factor
  `prime(i)` of `k` (with multiplicity), where `prime(1) = 2`. The index of a prime `p` is
  `Nat.primeCounting p = π(p)`. `parts k` lists them in weakly decreasing order
  `y_1 ≥ y_2 ≥ … ≥ y_m` (Mathlib's `Nat.primeFactorsList k` is increasing; it is reversed).
  `parts 1 = []` is the empty partition.
* *Young diagram.* `youngDiagram y` is the set of cells `(i, j)` (0-indexed row `i`, column
  `j`) with `i < m` and `j < y_{i+1}`: row `i` has `y_{i+1}` cells, left-justified.
* *Domino tilings.* A domino is a set of two edge-adjacent cells `{(i, j), (i + 1, j)}` or
  `{(i, j), (i, j + 1)}`. A set `S` of cells is `DominoTileable` if it is the union of a family
  of pairwise disjoint dominoes. (The empty diagram is tiled by the empty family, so `1` is a
  term.) `IsTerm k` says `k ≥ 1` and the Young diagram of the partition with Heinz number `k` is
  domino-tileable.
* *The sequence.* `a n = Nat.nth IsTerm (n - 1)`: the `n`-th term (offset `1`) is the `n`-th
  smallest element of `{k | IsTerm k}`. It is noncomputable as written (`Nat.nth`), but
  `IsTerm` is decidable. `tileL` is a search for a tiling (the row-major first cell of a set must
  be covered by a domino with its right neighbour or with the cell below it), and
  `isTerm_iff_isTermB` proves it correct. The data check transfers a kernel-checked
  `List.filter` over `0, …, 131` to `Nat.nth` (`map_nth_eq_of_filter`).
* *The conjecture.* "Odd parts appear as many times in even as in odd positions": with
  positions `1, …, m` of `(y_1, …, y_m)`, the number of `i` with `i` even and `y_i` odd equals
  the number of `i` with `i` odd and `y_i` odd (`OddPartsBalanced`). The entry's Mathematica and
  Maple programs list the parts in increasing order instead. Reversing a list of length `m` maps
  position `i` to `m + 1 - i`, which either keeps every parity or swaps all of them, so the
  condition is the same for both orders. `b n = Nat.nth IsConjTerm (n - 1)` is the increasing
  sequence of Heinz numbers of such partitions. The conjecture "this sequence is the Heinz numbers
  of [such] partitions" is read as `a n = b n` for every `n ≥ 1`. Both sets of terms are infinite
  (e.g. they contain `3 ^ e`, the Heinz number of `(2, 2, …, 2)`), so this is equivalent to
  `IsTerm k ↔ IsConjTerm k` for every `k`.
-/

namespace Math0.Statements.A300789

/-! ### Definitions -/

/-- The parts of the integer partition with Heinz number `k`, in weakly decreasing order: the
prime indices `π(p)` of the prime factors `p` of `k`, with multiplicity (`prime(π(p)) = p`). -/
def parts (k : ℕ) : List ℕ := (k.primeFactorsList.map Nat.primeCounting).reverse

/-- The Young diagram of the partition `y = (y_1, …, y_m)` (parts in weakly decreasing order):
the cells `(i, j)` (0-indexed) with `i < m` and `j < y_{i+1}`. -/
def youngDiagram (y : List ℕ) : Set (ℕ × ℕ) :=
  {c | c.1 < y.length ∧ c.2 < y.getD c.1 0}

/-- A domino: two edge-adjacent cells, vertical `{(i, j), (i + 1, j)}` or horizontal
`{(i, j), (i, j + 1)}`. -/
def IsDomino (d : Set (ℕ × ℕ)) : Prop :=
  ∃ i j : ℕ, d = {(i, j), (i + 1, j)} ∨ d = {(i, j), (i, j + 1)}

/-- `S` can be tiled by dominoes: it is the union of a family of pairwise disjoint dominoes. -/
def DominoTileable (S : Set (ℕ × ℕ)) : Prop :=
  ∃ D : Set (Set (ℕ × ℕ)), (∀ d ∈ D, IsDomino d) ∧ D.PairwiseDisjoint id ∧ ⋃₀ D = S

/-- `k` is a term of A300789: `k ≥ 1` is the Heinz number of an integer partition whose Young
diagram can be tiled by dominoes. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ DominoTileable (youngDiagram (parts k))

/-! ### A decision procedure for domino tileability -/

/-- Strict row-major (lexicographic) order on cells. -/
def LexLt (a b : ℕ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

/-- Search for a domino tiling of the cells of `l`, which are assumed to be listed in strictly
increasing row-major order. The first cell `c` must be covered by a domino with its right
neighbour or with the cell below it. `fuel ≥ l.length` only makes the recursion structural. -/
def tileL : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | fuel + 1, c :: rest =>
    (decide ((c.1, c.2 + 1) ∈ rest) && tileL fuel (rest.erase (c.1, c.2 + 1))) ||
      (decide ((c.1 + 1, c.2) ∈ rest) && tileL fuel (rest.erase (c.1 + 1, c.2)))

/-- The cells of the Young diagram of `y`, row by row (row-major order). -/
def cellsList (y : List ℕ) : List (ℕ × ℕ) :=
  (List.range y.length).flatMap fun i => (List.range (y.getD i 0)).map fun j => (i, j)

/-- Boolean version of `IsTerm` (see `isTerm_iff_isTermB`). -/
def isTermB (k : ℕ) : Bool :=
  decide (0 < k) && tileL (cellsList (parts k)).length (cellsList (parts k))

theorem tileable_empty : DominoTileable ∅ :=
  ⟨∅, by simp, Set.pairwiseDisjoint_empty, Set.sUnion_empty⟩

theorem tileable_of_diff {S d : Set (ℕ × ℕ)} (hd : IsDomino d) (hdS : d ⊆ S)
    (h : DominoTileable (S \ d)) : DominoTileable S := by
  obtain ⟨D, hD, hdisj, hU⟩ := h
  refine ⟨insert d D, ?_, ?_, ?_⟩
  · rintro e (rfl | he)
    exacts [hd, hD e he]
  · refine hdisj.insert fun e he _ => ?_
    have hsub : e ⊆ S \ d := hU ▸ Set.subset_sUnion_of_mem he
    exact Set.disjoint_left.2 fun x hx hx' => (hsub hx').2 hx
  · rw [Set.sUnion_insert, hU, Set.union_sdiff_cancel hdS]

theorem exists_domino_of_tileable {S : Set (ℕ × ℕ)} (h : DominoTileable S) {c : ℕ × ℕ}
    (hc : c ∈ S) : ∃ d, IsDomino d ∧ c ∈ d ∧ d ⊆ S ∧ DominoTileable (S \ d) := by
  obtain ⟨D, hD, hdisj, rfl⟩ := h
  obtain ⟨d, hdD, hcd⟩ := hc
  refine ⟨d, hD d hdD, hcd, Set.subset_sUnion_of_mem hdD, D \ {d}, fun e he => hD e he.1,
    hdisj.subset Set.sdiff_subset, ?_⟩
  ext x
  simp only [Set.mem_sUnion, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨e, ⟨heD, hne⟩, hxe⟩
    exact ⟨⟨e, heD, hxe⟩, fun hxd => Set.disjoint_left.1 (hdisj heD hdD hne) hxe hxd⟩
  · rintro ⟨⟨e, heD, hxe⟩, hxd⟩
    exact ⟨e, ⟨heD, fun h => hxd (h ▸ hxe)⟩, hxe⟩

/-- A domino containing the row-major first cell `c` of `S` and contained in `S` is
`{c, c + (0, 1)}` or `{c, c + (1, 0)}`. -/
theorem domino_at_min {S : Set (ℕ × ℕ)} {c : ℕ × ℕ} (hmin : ∀ x ∈ S, x ≠ c → LexLt c x)
    {d : Set (ℕ × ℕ)} (hd : IsDomino d) (hcd : c ∈ d) (hdS : d ⊆ S) :
    d = {c, (c.1, c.2 + 1)} ∨ d = {c, (c.1 + 1, c.2)} := by
  obtain ⟨i, j, rfl | rfl⟩ := hd
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcd
    rcases hcd with rfl | rfl
    · exact Or.inr rfl
    · exfalso
      have := hmin (i, j) (hdS (by simp)) (by simp)
      simp [LexLt] at this
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcd
    rcases hcd with rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have := hmin (i, j) (hdS (by simp)) (by simp)
      simp [LexLt] at this

theorem LexLt.ne {a b : ℕ × ℕ} (h : LexLt a b) : a ≠ b := by
  rintro rfl
  rcases h with h | ⟨-, h⟩ <;> exact lt_irrefl _ h

theorem tileL_iff : ∀ (fuel : ℕ) (l : List (ℕ × ℕ)), l.Pairwise LexLt → l.length ≤ fuel →
    (tileL fuel l = true ↔ DominoTileable {x | x ∈ l})
  | _, [], _, _ => by simp [tileL, tileable_empty]
  | 0, _ :: _, _, h => by simp at h
  | fuel + 1, c :: rest, hl, hlen => by
    have hcmin : ∀ x ∈ rest, LexLt c x := (List.pairwise_cons.1 hl).1
    have hrest : rest.Pairwise LexLt := (List.pairwise_cons.1 hl).2
    have hnd : rest.Nodup := hrest.imp LexLt.ne
    have hcnot : c ∉ rest := fun h => (hcmin c h).ne rfl
    have hset : ∀ x ∈ rest, {y | y ∈ rest.erase x} = {y | y ∈ c :: rest} \ {c, x} := by
      intro x _
      ext y
      simp only [Set.mem_ofPred_eq, hnd.mem_erase_iff, Set.mem_sdiff, List.mem_cons,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hyx, hy⟩
        exact ⟨Or.inr hy, fun h => h.elim (fun h => hcnot (h ▸ hy)) hyx⟩
      · rintro ⟨hy, hn⟩
        exact ⟨fun h => hn (Or.inr h), hy.resolve_left fun h => hn (Or.inl h)⟩
    have key : ∀ x ∈ rest, (tileL fuel (rest.erase x) = true ↔
        DominoTileable ({y | y ∈ c :: rest} \ {c, x})) := by
      intro x hx
      rw [← hset x hx]
      refine tileL_iff fuel _ (hrest.sublist List.erase_sublist) ?_
      rw [List.length_erase_of_mem hx]
      simp only [List.length_cons] at hlen
      omega
    have hsub : ∀ x ∈ rest, ({c, x} : Set (ℕ × ℕ)) ⊆ {y | y ∈ c :: rest} := by
      intro x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hx
    have hmin : ∀ x ∈ {y | y ∈ c :: rest}, x ≠ c → LexLt c x := by
      intro x hx hxc
      exact hcmin x ((List.mem_cons.1 hx).resolve_left hxc)
    have hmem : ∀ x, ({c, x} : Set (ℕ × ℕ)) ⊆ {y | y ∈ c :: rest} → x ≠ c → x ∈ rest := by
      intro x h hxc
      have : x ∈ c :: rest := h (by simp)
      exact (List.mem_cons.1 this).resolve_left hxc
    simp only [tileL, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨hx, ht⟩ | ⟨hx, ht⟩)
      · exact tileable_of_diff ⟨c.1, c.2, Or.inr rfl⟩ (hsub _ hx) ((key _ hx).1 ht)
      · exact tileable_of_diff ⟨c.1, c.2, Or.inl rfl⟩ (hsub _ hx) ((key _ hx).1 ht)
    · intro h
      obtain ⟨d, hd, hcd, hdS, hdt⟩ := exists_domino_of_tileable h List.mem_cons_self
      rcases domino_at_min hmin hd hcd hdS with rfl | rfl
      · have hx := hmem _ hdS (by simp [Prod.ext_iff])
        exact Or.inl ⟨hx, (key _ hx).2 hdt⟩
      · have hx := hmem _ hdS (by simp [Prod.ext_iff])
        exact Or.inr ⟨hx, (key _ hx).2 hdt⟩

theorem mem_cellsList {y : List ℕ} {c : ℕ × ℕ} : c ∈ cellsList y ↔ c ∈ youngDiagram y := by
  obtain ⟨i, j⟩ := c
  simp only [cellsList, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq,
    youngDiagram, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i', hi', j', hj', rfl, rfl⟩
    exact ⟨hi', hj'⟩
  · rintro ⟨hi, hj⟩
    exact ⟨i, hi, j, hj, rfl, rfl⟩

theorem pairwise_cellsList (y : List ℕ) : (cellsList y).Pairwise LexLt := by
  unfold cellsList
  rw [List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun h => Or.inr ⟨rfl, h⟩
  · refine List.pairwise_lt_range.imp fun h x hx z hz => ?_
    simp only [List.mem_map, List.mem_range] at hx hz
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hz
    exact Or.inl h

theorem setOf_mem_cellsList (y : List ℕ) : {x | x ∈ cellsList y} = youngDiagram y :=
  Set.ext fun _ => mem_cellsList

theorem isTerm_iff_isTermB (k : ℕ) : IsTerm k ↔ isTermB k = true := by
  rw [IsTerm, isTermB, Bool.and_eq_true, decide_eq_true_eq,
    tileL_iff _ _ (pairwise_cellsList _) le_rfl, setOf_mem_cellsList]

instance : DecidablePred IsTerm := fun k => decidable_of_iff _ (isTerm_iff_isTermB k).symm

/-! ### The sequence and the conjecture -/

/-- A300789: the `n`-th Heinz number (offset `1`, in increasing order) of an integer partition
whose Young diagram can be tiled by dominoes. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- The partition `y = (y_1, …, y_m)` has as many odd parts in even positions as in odd
positions: `#{i ∈ [1, m] | i even, y_i odd} = #{i ∈ [1, m] | i odd, y_i odd}` (here `i` is
0-indexed, so position `i + 1`). -/
def OddPartsBalanced (y : List ℕ) : Prop :=
  ((Finset.range y.length).filter fun i => Even (i + 1) ∧ Odd (y.getD i 0)).card =
    ((Finset.range y.length).filter fun i => Odd (i + 1) ∧ Odd (y.getD i 0)).card

/-- `k ≥ 1` is the Heinz number of a partition whose odd parts appear as many times in even as
in odd positions. -/
def IsConjTerm (k : ℕ) : Prop := 0 < k ∧ OddPartsBalanced (parts k)

instance : DecidablePred IsConjTerm := fun k => by
  unfold IsConjTerm OddPartsBalanced
  infer_instance

/-- The `n`-th Heinz number (offset `1`, in increasing order) of a partition whose odd parts
appear as many times in even as in odd positions. -/
noncomputable def b (n : ℕ) : ℕ := Nat.nth IsConjTerm (n - 1)

/-! ### Sanity checks -/

/-- The elements `< N` satisfying `p`, in increasing order, are `nth p 0, nth p 1, …`. -/
theorem filter_range_eq (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    (List.range N).filter (fun k => decide (p k)) =
      (List.range (Nat.count p N)).map (Nat.nth p) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, ih, Nat.count_succ]
    by_cases h : p N
    · simp [h, List.range_succ, Nat.nth_count h]
    · simp [h]

theorem map_nth_eq_of_filter {p : ℕ → Prop} [DecidablePred p] {N K : ℕ} {L : List ℕ}
    (h : (List.range N).filter (fun k => decide (p k)) = L) (hK : L.length = K) :
    (List.range K).map (Nat.nth p) = L := by
  rw [filter_range_eq] at h
  subst h
  simp only [List.length_map, List.length_range] at hK
  rw [hK]

/-- The entry's example: the partitions with Heinz numbers `1, 3, 4, …, 28` (the first fifteen
terms) are `(), (2), (11), (4), (22), (31), (211), (6), (1111), (8), (42), (51), (33), (222),
(411)` (kernel-checked). -/
theorem parts_example :
    [1, 3, 4, 7, 9, 10, 12, 13, 16, 19, 21, 22, 25, 27, 28].map parts =
      [[], [2], [1, 1], [4], [2, 2], [3, 1], [2, 1, 1], [6], [1, 1, 1, 1], [8], [4, 2], [5, 1],
        [3, 3], [2, 2, 2], [4, 1, 1]] := by
  decide +kernel

/-- The definition reproduces all 63 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 63).map (fun i => a (i + 1)) =
    [1, 3, 4, 7, 9, 10, 12, 13, 16, 19, 21, 22, 25, 27, 28, 29, 34, 36, 37, 39, 40, 43, 46, 48,
      49, 52, 53, 55, 57, 61, 62, 63, 64, 70, 71, 75, 76, 79, 81, 82, 84, 85, 87, 88, 89, 90, 91,
      94, 100, 101, 107, 108, 111, 112, 113, 115, 116, 117, 118, 121, 129, 130, 131] := by
  have : (fun i => a (i + 1)) = Nat.nth IsTerm := funext fun i => by simp [a]
  rw [this]
  exact map_nth_eq_of_filter (N := 132) (by decide +kernel) rfl

/-- The conjectured description also reproduces the 63 listed terms (as the entry's programs,
which use it, do; kernel-checked). -/
theorem b_data : (List.range 63).map (fun i => b (i + 1)) =
    [1, 3, 4, 7, 9, 10, 12, 13, 16, 19, 21, 22, 25, 27, 28, 29, 34, 36, 37, 39, 40, 43, 46, 48,
      49, 52, 53, 55, 57, 61, 62, 63, 64, 70, 71, 75, 76, 79, 81, 82, 84, 85, 87, 88, 89, 90, 91,
      94, 100, 101, 107, 108, 111, 112, 113, 115, 116, 117, 118, 121, 129, 130, 131] := by
  have : (fun i => b (i + 1)) = Nat.nth IsConjTerm := funext fun i => by simp [b]
  rw [this]
  exact map_nth_eq_of_filter (N := 132) (by decide +kernel) rfl

/-- Conjecture (Wiseman, A300789): the sequence of Heinz numbers of integer partitions whose
Young diagram can be tiled by dominoes is the sequence of Heinz numbers of integer partitions in
which the odd parts appear as many times in even as in odd positions, i.e. `a(n) = b(n)` for
every `n ≥ 1`. -/
def statement : Prop := ∀ n : ℕ, 1 ≤ n → a n = b n

end Math0.Statements.A300789
