/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A308359: fixed polyominoes with `n` cells and width `n - 2`

Source: https://oeis.org/A308359, _R. J. Mathar_, May 22 2019 (FORMULA section). Verbatim:
> Conjecture: T(n,n-2) = 8*n^2 - 51*n + 86 for n >= 5.

The entry is "Triangle T(n,w) read by rows: the number of fixed polyominoes with n cells and
width w of the convex hull." (offset `1`, rows `n ≥ 1`, `1 ≤ w ≤ n`).

## Encoding

* *Fixed polyominoes.* A fixed polyomino with `n` cells is a set of `n` unit cells of the square
  grid, connected through shared edges, counted up to translation only (rotations and
  reflections give different fixed polyominoes). Every translation class of a finite nonempty set
  of cells of `ℤ × ℤ` contains exactly one set lying in `ℕ × ℕ` that meets both the line `x = 0`
  and the line `y = 0`. So a fixed polyomino with `n` cells is encoded by such a normalized
  set `S : Finset (ℕ × ℕ)`: `S.card = n`, some cell has `x = 0`, some cell has `y = 0`, and `S`
  is edge-connected (`IsConnected`: any two cells of `S` are joined by a chain of cells of `S`,
  consecutive ones sharing an edge (`Adj`)). Cells are written `(x, y)`, `x` the column.
* *Width.* The convex hull of the union of the unit squares of `S` spans the columns
  `min x, …, max x`, so its width is `max x - min x + 1 = S.sup Prod.fst + 1` (`min x = 0`).
  Only the width is prescribed; the height is unrestricted. (The entry's comment says that the
  height `h` ranges over `w ≤ h ≤ n`, but the entry itself contradicts this: its formula
  `T(n,n-1) = 4*n-8` counts shapes of "width n-1 and height 2", the listed `T(4,3) = 8` counts the
  L, T and S/Z tetrominoes of height `2`, and the row sums are the total numbers of fixed
  polyominoes, A001168, which the entry cross-references.)
* `T n w` is the number of such sets (`Set.ncard`, noncomputable). `T_eq_Tbox` proves that every
  such set lies in the box `[0, w) × [0, n + 1 - w)`, so `T n w = Tbox n w`, a computable count
  over the `n`-element subsets of that box. Connectivity is decided by a flood fill on bit masks
  (`connBits`: the cell `(x, y)` is bit `x * D + y` with `D = max y + 2`, so that steps along a
  column never wrap into the next column), proved equivalent to `IsConnected`
  (`isConnected_iff_bits`, via the flood fill on finsets, `grow_eq_iff`); this keeps the kernel
  computation fast.
* The triangle is read by rows (offset `1`): `a (n * (n - 1) / 2 + w) = T n w` for
  `1 ≤ w ≤ n` (`a_eq_T`). `a_data` checks the first 23 listed terms (rows `1..6`, then
  `T(7,1) = 1`, `T(7,2) = 66`) in the kernel, in four pieces to keep its memory use small. The
  next term, `T(7,3)`, ranges over `C(15,7) = 6435` subsets and is out of reach of a quick check.
* The conjecture is stated for every `n ≥ 5` (then `w = n - 2 ≥ 3`) in `ℤ`, so the right side
  `8n² - 51n + 86` is not truncated (it is positive anyway).
-/

namespace Math0.Statements.A308359

/-! ### Fixed polyominoes -/

/-- Two cells `p = (x, y)` and `q` of the grid share an edge. -/
def Adj (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨ (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

instance : DecidableRel Adj := fun p q =>
  inferInstanceAs (Decidable ((p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
    (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))))

/-- A step between two edge-adjacent cells of `S`. -/
def Step (S : Finset (ℕ × ℕ)) (p q : ℕ × ℕ) : Prop := p ∈ S ∧ q ∈ S ∧ Adj p q

/-- `S` is edge-connected: any two cells of `S` are joined by a chain of cells of `S` in which
consecutive cells share an edge. -/
def IsConnected (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, Relation.ReflTransGen (Step S) p q

/-- `S` is (the normalized representative of) a fixed polyomino with `n` cells and width `w`:
`n` cells, translated so that the least column and the least row are `0`, edge-connected, with
columns `0, …, w - 1` spanned by its convex hull (`max x + 1 = w`). -/
def IsPoly (n w : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  S.card = n ∧ (∃ p ∈ S, p.1 = 0) ∧ (∃ p ∈ S, p.2 = 0) ∧ S.sup Prod.fst + 1 = w ∧ IsConnected S

/-- A308359: `T(n, w)` is the number of fixed polyominoes with `n` cells whose convex hull has
width `w`. -/
noncomputable def T (n w : ℕ) : ℕ := {S : Finset (ℕ × ℕ) | IsPoly n w S}.ncard

/-! ### Connectivity by a flood fill -/

/-- Add to `R` the cells of `S` that share an edge with a cell of `R`. -/
def step (S R : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := R ∪ S.filter fun c => ∃ b ∈ R, Adj b c

/-- `k` rounds of `step`. -/
def grow (S : Finset (ℕ × ℕ)) : ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ)
  | 0, R => R
  | k + 1, R => grow S k (step S R)

theorem adj_symm {p q : ℕ × ℕ} (h : Adj p q) : Adj q p := by
  unfold Adj at *
  omega

theorem step_symm {S : Finset (ℕ × ℕ)} {p q : ℕ × ℕ} (h : Step S p q) : Step S q p :=
  ⟨h.2.1, h.1, adj_symm h.2.2⟩

theorem reach_symm {S : Finset (ℕ × ℕ)} {p q : ℕ × ℕ}
    (h : Relation.ReflTransGen (Step S) p q) : Relation.ReflTransGen (Step S) q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (step_symm hbc) ih

theorem subset_step (S R : Finset (ℕ × ℕ)) : R ⊆ step S R := Finset.subset_union_left

theorem step_subset {S R : Finset (ℕ × ℕ)} (h : R ⊆ S) : step S R ⊆ S :=
  Finset.union_subset h (Finset.filter_subset _ _)

theorem grow_subset {S : Finset (ℕ × ℕ)} :
    ∀ (k : ℕ) {R : Finset (ℕ × ℕ)}, R ⊆ S → grow S k R ⊆ S
  | 0, _, h => h
  | k + 1, _, h => grow_subset k (step_subset h)

theorem mem_grow_of_mem {S : Finset (ℕ × ℕ)} :
    ∀ (k : ℕ) {R : Finset (ℕ × ℕ)} {x : ℕ × ℕ}, x ∈ R → x ∈ grow S k R
  | 0, _, _, h => h
  | k + 1, _, _, h => mem_grow_of_mem k (subset_step S _ h)

/-- Everything the flood fill reaches is reachable from `r` inside `S`. -/
theorem grow_reach {S : Finset (ℕ × ℕ)} {r : ℕ × ℕ} :
    ∀ (k : ℕ) {R : Finset (ℕ × ℕ)}, R ⊆ S → (∀ x ∈ R, Relation.ReflTransGen (Step S) r x) →
      ∀ x ∈ grow S k R, Relation.ReflTransGen (Step S) r x
  | 0, _, _, h => h
  | k + 1, R, hR, h => by
    refine grow_reach k (step_subset hR) fun x hx => ?_
    rcases Finset.mem_union.1 hx with hx | hx
    · exact h x hx
    · obtain ⟨hxS, b, hb, hbx⟩ := Finset.mem_filter.1 hx
      exact (h b hb).tail ⟨hR hb, hxS, hbx⟩

theorem grow_fix {S R : Finset (ℕ × ℕ)} (h : step S R = R) : ∀ k, grow S k R = R
  | 0 => rfl
  | k + 1 => by rw [grow, h, grow_fix h k]

/-- After `k` rounds the flood fill has gained `k` cells or has stopped growing. -/
theorem grow_card_or_closed {S : Finset (ℕ × ℕ)} :
    ∀ (k : ℕ) (R : Finset (ℕ × ℕ)),
      R.card + k ≤ (grow S k R).card ∨ step S (grow S k R) = grow S k R
  | 0, _ => Or.inl le_rfl
  | k + 1, R => by
    by_cases hR : step S R = R
    · right
      rw [grow_fix hR]
      exact hR
    · rcases grow_card_or_closed (S := S) k (step S R) with h | h
      · left
        have hlt : R.card < (step S R).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_step S R, Ne.symm hR⟩)
        change R.card + (k + 1) ≤ (grow S k (step S R)).card
        omega
      · right
        exact h

/-- If a chain inside `S` leaves `A`, some cell of `S` outside `A` is adjacent to a cell of
`A`. -/
theorem frontier {S A : Finset (ℕ × ℕ)} {a q : ℕ × ℕ} (ha : a ∈ A) (hq : q ∉ A)
    (h : Relation.ReflTransGen (Step S) a q) : ∃ b ∈ A, ∃ c ∈ S, c ∉ A ∧ Adj b c := by
  induction h with
  | refl => exact absurd ha hq
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ A
    · exact ⟨b, hb, c, hbc.2.1, hq, hbc.2.2⟩
    · exact ih hb

/-- `S` is connected iff the flood fill from any one of its cells reaches all of `S` within
`S.card` rounds. -/
theorem grow_eq_iff {S : Finset (ℕ × ℕ)} {r : ℕ × ℕ} (hr : r ∈ S) :
    grow S S.card {r} = S ↔ IsConnected S := by
  have hsub : grow S S.card {r} ⊆ S := grow_subset _ (by simpa using hr)
  constructor
  · intro heq
    have hreach : ∀ x ∈ S, Relation.ReflTransGen (Step S) r x := by
      intro x hx
      rw [← heq] at hx
      refine grow_reach _ (by simpa using hr) (fun y hy => ?_) x hx
      rw [Finset.mem_singleton.1 hy]
    intro p hp q hq
    exact (reach_symm (hreach p hp)).trans (hreach q hq)
  · intro h
    have hclosed : step S (grow S S.card {r}) = grow S S.card {r} := by
      rcases grow_card_or_closed (S := S) S.card {r} with h' | h'
      · have := Finset.card_le_card hsub
        simp at h'
        omega
      · exact h'
    have hSsub : S ⊆ grow S S.card {r} := by
      intro q hq
      by_contra hqG
      obtain ⟨b, hb, c, hc, hcG, hbc⟩ :=
        frontier (mem_grow_of_mem S.card (Finset.mem_singleton_self r)) hqG (h r hr q hq)
      apply hcG
      rw [← hclosed]
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hc, b, hb, hbc⟩)
    exact Finset.Subset.antisymm hsub hSsub

/-! ### The same flood fill on bit masks (for fast evaluation in the kernel) -/

/-- The bit of the cell `c = (x, y)` in a mask with `D` bits per column. -/
def idx (D : ℕ) (c : ℕ × ℕ) : ℕ := c.1 * D + c.2

/-- The bit mask of a set of cells. -/
def enc (D : ℕ) (A : Finset (ℕ × ℕ)) : ℕ := ∑ c ∈ A, 2 ^ idx D c

/-- One round of the flood fill on masks: add to `R` the cells of `m` next to a cell of `R`
(shifts by `1` move along a column, shifts by `D` move along a row). -/
def bstep (D m R : ℕ) : ℕ := R ||| (m &&& ((R <<< 1) ||| (R >>> 1) ||| (R <<< D) ||| (R >>> D)))

/-- `k` rounds of `bstep`. -/
def bgrow (D m : ℕ) : ℕ → ℕ → ℕ
  | 0, R => R
  | k + 1, R => bgrow D m k (bstep D m R)

/-- The column stride used for `S`: two more than its largest row index, so that every column
of the mask has an empty top bit and the shifts by `1` never connect two columns. -/
def stride (S : Finset (ℕ × ℕ)) : ℕ := S.sup Prod.snd + 2

/-- The flood fill on masks, started from the cell of `S` at the highest bit of its mask,
reaches all of `S` within `S.card` rounds. -/
def connBits (S : Finset (ℕ × ℕ)) : Prop :=
  bgrow (stride S) (enc (stride S) S) S.card (2 ^ Nat.log2 (enc (stride S) S)) =
    enc (stride S) S

instance : DecidablePred connBits := fun S =>
  inferInstanceAs (Decidable (bgrow (stride S) (enc (stride S) S) S.card
    (2 ^ Nat.log2 (enc (stride S) S)) = enc (stride S) S))

theorem idx_inj {D : ℕ} {b c : ℕ × ℕ} (hb : b.2 < D) (hc : c.2 < D)
    (h : idx D b = idx D c) : b = c := by
  unfold idx at h
  have hD : 0 < D := by omega
  have h1 : (D * b.1 + b.2) / D = (D * c.1 + c.2) / D := by rw [Nat.mul_comm D, Nat.mul_comm D, h]
  have h2 : (D * b.1 + b.2) % D = (D * c.1 + c.2) % D := by rw [Nat.mul_comm D, Nat.mul_comm D, h]
  rw [Nat.mul_add_div hD, Nat.mul_add_div hD, Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hc] at h1
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc] at h2
  exact Prod.ext (by omega) h2

theorem testBit_enc {D : ℕ} {A : Finset (ℕ × ℕ)} (hA : ∀ c ∈ A, c.2 < D) (j : ℕ) :
    (enc D A).testBit j = true ↔ ∃ c ∈ A, idx D c = j := by
  have hinj : Set.InjOn (idx D) A := fun b hb c hc h => idx_inj (hA b hb) (hA c hc) h
  have he : enc D A = ∑ i ∈ A.image (idx D), 2 ^ i := by
    rw [enc, Finset.sum_image hinj]
  rw [he, ← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow,
    Finset.mem_image]

theorem enc_inj {D : ℕ} {A B : Finset (ℕ × ℕ)} (hA : ∀ c ∈ A, c.2 < D)
    (hB : ∀ c ∈ B, c.2 < D) (h : enc D A = enc D B) : A = B := by
  have key : ∀ {A B : Finset (ℕ × ℕ)}, (∀ c ∈ A, c.2 < D) → (∀ c ∈ B, c.2 < D) →
      enc D A = enc D B → A ⊆ B := by
    intro A B hA hB h c hc
    have hc' := (testBit_enc hA (idx D c)).2 ⟨c, hc, rfl⟩
    rw [h] at hc'
    obtain ⟨c', hc'B, he⟩ := (testBit_enc hB _).1 hc'
    rwa [← idx_inj (hB c' hc'B) (hA c hc) he]
  exact Finset.Subset.antisymm (key hA hB h) (key hB hA h.symm)

/-- Adjacent cells are the cells whose bits differ by `1` or by `D` (rows below `D - 1`). -/
theorem adj_iff_idx {D : ℕ} {b c : ℕ × ℕ} (hb : b.2 + 2 ≤ D) (hc : c.2 + 2 ≤ D) :
    Adj b c ↔ idx D b + 1 = idx D c ∨ idx D c + 1 = idx D b ∨ idx D b + D = idx D c ∨
      idx D c + D = idx D b := by
  constructor
  · intro h
    unfold Adj at h
    unfold idx
    rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
    · rw [h1]; omega
    · rw [h1]; omega
    · rw [← h2, Nat.add_mul, h1]; omega
    · rw [← h2, Nat.add_mul, h1]; omega
  · intro h
    unfold Adj
    rcases h with h | h | h | h
    · have := idx_inj (D := D) (b := (b.1, b.2 + 1)) (c := c) (by simp; omega) (by omega)
        (by unfold idx at *; simp only; omega)
      rw [← this]; simp
    · have := idx_inj (D := D) (b := (c.1, c.2 + 1)) (c := b) (by simp; omega) (by omega)
        (by unfold idx at *; simp only; omega)
      rw [← this]; simp
    · have := idx_inj (D := D) (b := (b.1 + 1, b.2)) (c := c) (by simp; omega) (by omega)
        (by unfold idx at *; simp only [Nat.add_mul]; omega)
      rw [← this]; simp
    · have := idx_inj (D := D) (b := (c.1 + 1, c.2)) (c := b) (by simp; omega) (by omega)
        (by unfold idx at *; simp only [Nat.add_mul]; omega)
      rw [← this]; simp

theorem bstep_enc {D : ℕ} {S A : Finset (ℕ × ℕ)} (hS : ∀ c ∈ S, c.2 + 2 ≤ D) (hA : A ⊆ S) :
    bstep D (enc D S) (enc D A) = enc D (step S A) := by
  have hS' : ∀ c ∈ S, c.2 < D := fun c hc => by have := hS c hc; omega
  have hA' : ∀ c ∈ A, c.2 < D := fun c hc => hS' c (hA hc)
  have hT' : ∀ c ∈ step S A, c.2 < D := fun c hc => hS' c (step_subset hA hc)
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.2
  rw [bstep, testBit_enc hT']
  simp only [Nat.testBit_lor, Nat.testBit_land, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, testBit_enc hA', testBit_enc hS']
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨⟨c, hc, rfl⟩, h⟩)
    · exact ⟨c, subset_step S A hc, rfl⟩
    · refine ⟨c, Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hc, ?_⟩), rfl⟩
      rcases h with (((⟨h1, b, hb, hbj⟩ | ⟨b, hb, hbj⟩) | ⟨h1, b, hb, hbj⟩) | ⟨b, hb, hbj⟩)
      · exact ⟨b, hb, (adj_iff_idx (hS b (hA hb)) (hS c hc)).2 (Or.inl (by omega))⟩
      · exact ⟨b, hb, (adj_iff_idx (hS b (hA hb)) (hS c hc)).2 (Or.inr (Or.inl (by omega)))⟩
      · exact ⟨b, hb, (adj_iff_idx (hS b (hA hb)) (hS c hc)).2
          (Or.inr (Or.inr (Or.inl (by omega))))⟩
      · exact ⟨b, hb, (adj_iff_idx (hS b (hA hb)) (hS c hc)).2
          (Or.inr (Or.inr (Or.inr (by omega))))⟩
  · rintro ⟨c, hc, rfl⟩
    rcases Finset.mem_union.1 hc with hc | hc
    · exact Or.inl ⟨c, hc, rfl⟩
    · obtain ⟨hcS, b, hb, hbc⟩ := Finset.mem_filter.1 hc
      refine Or.inr ⟨⟨c, hcS, rfl⟩, ?_⟩
      rcases (adj_iff_idx (hS b (hA hb)) (hS c hcS)).1 hbc with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨by omega, b, hb, by omega⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨b, hb, by omega⟩))
      · exact Or.inl (Or.inr ⟨by omega, b, hb, by omega⟩)
      · exact Or.inr ⟨b, hb, by omega⟩

theorem bgrow_enc {D : ℕ} {S : Finset (ℕ × ℕ)} (hS : ∀ c ∈ S, c.2 + 2 ≤ D) :
    ∀ (k : ℕ) {A : Finset (ℕ × ℕ)}, A ⊆ S → bgrow D (enc D S) k (enc D A) = enc D (grow S k A)
  | 0, _, _ => rfl
  | k + 1, A, hA => by
    rw [bgrow, bstep_enc hS hA, grow]
    exact bgrow_enc hS k (step_subset hA)

theorem connBits_iff {S : Finset (ℕ × ℕ)} (hne : S.Nonempty) : connBits S ↔ IsConnected S := by
  have hS : ∀ c ∈ S, c.2 + 2 ≤ stride S := fun c hc => by
    have := Finset.le_sup (f := Prod.snd) hc
    unfold stride
    omega
  have hS' : ∀ c ∈ S, c.2 < stride S := fun c hc => by have := hS c hc; omega
  have hm : enc (stride S) S ≠ 0 := by
    obtain ⟨c, hc⟩ := hne
    intro h0
    have := (testBit_enc hS' (idx (stride S) c)).2 ⟨c, hc, rfl⟩
    rw [h0, Nat.zero_testBit] at this
    exact Bool.false_ne_true this
  obtain ⟨r, hr, hrm⟩ := (testBit_enc hS' _).1 (Nat.testBit_log2 hm)
  have h1 : 2 ^ Nat.log2 (enc (stride S) S) = enc (stride S) {r} := by
    rw [← hrm]
    simp only [enc, Finset.sum_singleton]
  have hr' : ({r} : Finset (ℕ × ℕ)) ⊆ S := by simpa using hr
  unfold connBits
  rw [h1, bgrow_enc hS _ hr', ← grow_eq_iff hr]
  exact ⟨enc_inj (fun c hc => hS' c (grow_subset _ hr' hc)) hS', fun h => by rw [h]⟩

theorem isConnected_iff_bits (S : Finset (ℕ × ℕ)) : S.card = 0 ∨ connBits S ↔ IsConnected S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, true_or, true_iff]
    intro p hp
    simp at hp
  · rw [connBits_iff hne]
    have := hne.card_pos
    exact ⟨fun h => h.resolve_left (by omega), Or.inr⟩

instance : DecidablePred IsConnected := fun S => decidable_of_iff _ (isConnected_iff_bits S)

instance (n w : ℕ) : DecidablePred (IsPoly n w) := fun S =>
  inferInstanceAs (Decidable (S.card = n ∧ (∃ p ∈ S, p.1 = 0) ∧ (∃ p ∈ S, p.2 = 0) ∧
    S.sup Prod.fst + 1 = w ∧ IsConnected S))

/-! ### A polyomino with `n` cells and width `w` fits in a `w × (n + 1 - w)` box -/

/-- Along a chain inside `S`, a coordinate `f` that changes by at most one per step takes every
intermediate value on some cell of `S`. -/
theorem exists_coord {S : Finset (ℕ × ℕ)} (f : ℕ × ℕ → ℕ)
    (hf : ∀ p q, Adj p q → f q ≤ f p + 1) {a b : ℕ × ℕ} (ha : a ∈ S)
    (hab : Relation.ReflTransGen (Step S) a b) :
    ∀ k, f a ≤ k → k ≤ f b → ∃ c ∈ S, f c = k := by
  induction hab with
  | refl =>
    intro k h1 h2
    exact ⟨a, ha, by omega⟩
  | @tail b c _ hbc ih =>
    intro k h1 h2
    by_cases hk : k ≤ f b
    · exact ih k h1 hk
    · have := hf b c hbc.2.2
      exact ⟨c, hbc.2.1, by omega⟩

/-- A connected set of cells occupying `C` columns and `R` rows has at least `C + R - 1`
cells. -/
theorem cols_add_rows_le {S : Finset (ℕ × ℕ)} (hS : IsConnected S) (hne : S.Nonempty) :
    (S.image Prod.fst).card + (S.image Prod.snd).card ≤ S.card + 1 := by
  obtain ⟨s, hs⟩ := hne
  have key : ∀ k, k + 1 ≤ S.card → ∃ A ⊆ S, A.card = k + 1 ∧
      (A.image Prod.fst).card + (A.image Prod.snd).card ≤ k + 2 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨{s}, by simpa using hs, by simp, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨A, hAS, hAc, hAb⟩ := ih (by omega)
      have hq : ∃ q ∈ S, q ∉ A := by
        by_contra hcon
        have hSA : S ⊆ A := fun q hq => by
          by_contra hqA
          exact hcon ⟨q, hq, hqA⟩
        have := Finset.card_le_card hSA
        omega
      obtain ⟨q, hqS, hqA⟩ := hq
      obtain ⟨a, haA⟩ : A.Nonempty := by
        rw [← Finset.card_pos]
        omega
      obtain ⟨b, hbA, c, hcS, hcA, hbc⟩ := frontier haA hqA (hS a (hAS haA) q hqS)
      refine ⟨insert c A, Finset.insert_subset hcS hAS, by
        rw [Finset.card_insert_of_notMem hcA, hAc], ?_⟩
      rw [Finset.image_insert, Finset.image_insert]
      have h1 := Finset.card_insert_le c.1 (A.image Prod.fst)
      have h2 := Finset.card_insert_le c.2 (A.image Prod.snd)
      rcases hbc with ⟨h, -⟩ | ⟨h, -⟩
      · have hm : c.1 ∈ A.image Prod.fst := Finset.mem_image.2 ⟨b, hbA, h⟩
        rw [Finset.card_insert_of_mem hm]
        omega
      · have hm : c.2 ∈ A.image Prod.snd := Finset.mem_image.2 ⟨b, hbA, h⟩
        rw [Finset.card_insert_of_mem hm]
        omega
  have hpos := Finset.card_pos.2 ⟨s, hs⟩
  obtain ⟨A, hAS, hAc, hAb⟩ := key (S.card - 1) (by omega)
  have hA : A = S := Finset.eq_of_subset_of_card_le hAS (by omega)
  subst hA
  omega

/-- The search box `[0, w) × [0, n + 1 - w)`. -/
def box (n w : ℕ) : Finset (ℕ × ℕ) := Finset.range w ×ˢ Finset.range (n + 1 - w)

theorem subset_box {n w : ℕ} {S : Finset (ℕ × ℕ)} (h : IsPoly n w S) : S ⊆ box n w := by
  obtain ⟨hcard, ⟨p0, hp0S, hp0⟩, ⟨q0, hq0S, hq0⟩, hsup, hconn⟩ := h
  have hne : S.Nonempty := ⟨p0, hp0S⟩
  obtain ⟨m, hmS, hm⟩ := Finset.exists_mem_eq_sup S hne Prod.fst
  have hfst : ∀ p q : ℕ × ℕ, Adj p q → q.1 ≤ p.1 + 1 := by
    intro p q h
    unfold Adj at h
    omega
  have hsnd : ∀ p q : ℕ × ℕ, Adj p q → q.2 ≤ p.2 + 1 := by
    intro p q h
    unfold Adj at h
    omega
  have hcols : Finset.range w ⊆ S.image Prod.fst := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨c, hc, hck⟩ :=
      exists_coord Prod.fst hfst hp0S (hconn p0 hp0S m hmS) k (by omega) (by omega)
    exact Finset.mem_image.2 ⟨c, hc, hck⟩
  have hbound := cols_add_rows_le hconn hne
  have hw := Finset.card_le_card hcols
  rw [Finset.card_range] at hw
  intro p hp
  have hp1 : p.1 ≤ S.sup Prod.fst := Finset.le_sup (f := Prod.fst) hp
  have hrows : Finset.range (p.2 + 1) ⊆ S.image Prod.snd := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨c, hc, hck⟩ :=
      exists_coord Prod.snd hsnd hq0S (hconn q0 hq0S p hp) k (by omega) (by omega)
    exact Finset.mem_image.2 ⟨c, hc, hck⟩
  have hh := Finset.card_le_card hrows
  rw [Finset.card_range] at hh
  rw [box, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  omega

/-- A computable count of the fixed polyominoes with `n` cells and width `w`: those
`n`-element subsets of the box that are normalized polyominoes of width `w`. -/
def Tbox (n w : ℕ) : ℕ := (((box n w).powersetCard n).filter (IsPoly n w)).card

theorem T_eq_Tbox (n w : ℕ) : T n w = Tbox n w := by
  rw [T, Tbox, ← Set.ncard_coe_finset]
  congr 1
  ext S
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_powersetCard]
  exact ⟨fun h => ⟨⟨subset_box h, h.1⟩, h⟩, fun h => h.2⟩

/-! ### The triangle read by rows -/

/-- Position `k` of row `n` (`1 ≤ k ≤ n`) and the following positions of rows `n + 1, …`:
returns the (row, column) of the `k`-th entry counted from the start of row `n`. -/
def pos : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, k, n => (n, k)
  | fuel + 1, k, n => if k ≤ n then (n, k) else pos fuel (k - n) (n + 1)

/-- A308359 as a sequence (offset `1`): the triangle `T(n, w)`, `1 ≤ w ≤ n`, read by rows. -/
def a (k : ℕ) : ℕ := Tbox (pos k k 1).1 (pos k k 1).2

theorem pos_eq : ∀ (d j fuel w : ℕ), 1 ≤ w → w ≤ j + d → d < fuel →
    pos fuel (w + ∑ i ∈ Finset.range d, (j + i)) j = (j + d, w)
  | 0, j, fuel + 1, w, _, h2, _ => by simp [pos, show w ≤ j by omega]
  | d + 1, j, fuel + 1, w, h1, h2, h3 => by
    rw [Finset.sum_range_succ']
    have hs : ∑ i ∈ Finset.range d, (j + (i + 1)) = ∑ i ∈ Finset.range d, (j + 1 + i) :=
      Finset.sum_congr rfl fun i _ => by omega
    rw [hs, pos, if_neg (by omega)]
    rw [show w + (∑ i ∈ Finset.range d, (j + 1 + i) + (j + 0)) - j =
      w + ∑ i ∈ Finset.range d, (j + 1 + i) by omega]
    rw [pos_eq d (j + 1) fuel w h1 (by omega) (by omega)]
    simp only [Prod.mk.injEq, and_true]
    omega

/-- `a` reads the triangle by rows: `a (n(n-1)/2 + w) = T(n, w)` for `1 ≤ w ≤ n`. -/
theorem a_eq_T {n w : ℕ} (hw : 1 ≤ w) (hwn : w ≤ n) : a (n * (n - 1) / 2 + w) = T n w := by
  have hsum : ∑ i ∈ Finset.range (n - 1), (1 + i) = n * (n - 1) / 2 := by
    rw [← Finset.sum_range_id, show n = (n - 1) + 1 by omega, Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_congr rfl fun i _ => (Nat.add_comm i 1).symm]
    simp
  have hge : n - 1 ≤ ∑ i ∈ Finset.range (n - 1), (1 + i) := by
    rw [Finset.sum_add_distrib]
    simp
  have hk : pos (n * (n - 1) / 2 + w) (n * (n - 1) / 2 + w) 1 = (n, w) := by
    have := pos_eq (n - 1) 1 (n * (n - 1) / 2 + w) w hw (by omega) (by omega)
    rw [hsum, show 1 + (n - 1) = n by omega, Nat.add_comm w] at this
    exact this
  rw [a, hk, T_eq_Tbox]

/-! ### The listed terms

The check is split into four kernel computations (rows `1..5`, two halves of row `6`, the start
of row `7`) so that each one stays small in memory. -/

theorem a_data_rows_one_to_five : (List.range 15).map (fun i => a (i + 1)) =
    [1, 1, 1, 1, 4, 1, 1, 9, 8, 1, 1, 18, 31, 12, 1] := by
  decide +kernel

theorem a_data_row_six_a : (List.range 3).map (fun i => a (i + 16)) = [1, 35, 95] := by
  decide +kernel

theorem a_data_row_six_b : (List.range 3).map (fun i => a (i + 19)) = [68, 16, 1] := by
  decide +kernel

theorem a_data_row_seven : (List.range 2).map (fun i => a (i + 22)) = [1, 66] := by
  decide +kernel

/-- The definition reproduces the first 23 listed terms: rows `1..6` and `T(7,1)`, `T(7,2)`
(kernel-checked, in the four pieces above). -/
theorem a_data : (List.range 23).map (fun i => a (i + 1)) =
    [1, 1, 1, 1, 4, 1, 1, 9, 8, 1, 1, 18, 31, 12, 1, 1, 35, 95, 68, 16, 1, 1, 66] := by
  have e : (List.range 23).map (fun i => a (i + 1)) =
      (List.range 15).map (fun i => a (i + 1)) ++ (List.range 3).map (fun i => a (i + 16)) ++
        (List.range 3).map (fun i => a (i + 19)) ++ (List.range 2).map (fun i => a (i + 22)) := by
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append]
  rw [e, a_data_rows_one_to_five, a_data_row_six_a, a_data_row_six_b, a_data_row_seven]
  rfl

/-! ### The conjecture -/

/-- Conjecture (Mathar, A308359): for every `n ≥ 5`, the number of fixed polyominoes with `n`
cells and width `n - 2` is `T(n, n - 2) = 8n² - 51n + 86`. -/
def statement : Prop :=
  ∀ n : ℕ, 5 ≤ n → (T n (n - 2) : ℤ) = 8 * (n : ℤ) ^ 2 - 51 * n + 86

end Math0.Statements.A308359
