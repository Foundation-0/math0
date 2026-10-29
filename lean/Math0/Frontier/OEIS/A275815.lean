/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A275815
import Math0.Audit

/-!
# A275815: Jones's conjecture `a(n) = 8 (n - 2)²` for `n ≥ 6` holds

The maximum total number of moves of same-colored queens on an `n × n` board is
`8 (n - 2)²` for every `n ≥ 6`.

**Lower bound.** On the border placement (all `4n - 4` border squares occupied) every interior
square is empty and sees a queen in each of the eight directions, so the queens have
`8 (n - 2)²` moves.

**Upper bound: a flow (linear programming dual) argument.** This part follows the proof of
A278212 in `Math0.Frontier.OEIS.A278212`, whose private lemmas are reproduced here for the
definitions of A275815. Fix a moving direction `d`. The moves in direction `d` are in bijection
with the empty squares `c` that "see" a queen behind them, i.e. `c - k • d` is a queen and
`c, c - d, …, c - (k-1) • d` are empty (`sum_ray_eq`). The indicator `Y c` of this satisfies
`Y c ≤ 1 - x c` and `Y c ≤ x (c - d) + Y (c - d)`, where `x` is the occupancy indicator. Let
`G c ≥ 0` be a "flow" from `c` to `c - d` (zero unless both are on the board) with
`α c := D + G (c + d) - G c ≥ 0`. Combining the two inequalities with weights `α c` and `G c`
and summing over the board, the flow terms telescope (`dir_ineq`). Summing over the directions
(`key`): `D · totalMoves ≤ ∑ c, (if c is occupied then B c else A c)` with
`A c = ∑_d α_d c` and `B c = ∑_d G_d (c + d)`, hence `≤ ∑ c, max (A c) (B c)`.

For `n ≥ 7` one flow table (`LQ`, depending only on the position class of a square) gives
exactly `D · 8 (n - 2)²` (`queen_ge8` via a class-counting argument, `queen7` directly).
For `n = 6` the linear relaxation only gives `132.8`; a branch and bound tree on the five
squares `(0, 1), (1, 5), (4, 5), (5, 4), (4, 0)` has eight leaves, and at each leaf a flow
certificate (found by integer linear programming, checked by the kernel, `leaf`) bounds the
number of moves by a value `< 129`, hence by `128` (`queen6_le`).
-/

namespace Math0.Frontier.A275815
open Math0.Statements.A275815

/-- The total number of moves of pieces of `S` moving in the directions `dirs`; for the queen
directions this is `totalMoves`. -/
private def tm (dirs : List (ℤ × ℤ)) (n : ℕ) (S : Finset (ℕ × ℕ)) : ℕ :=
  ∑ p ∈ S, (dirs.map (rayMoves n S p)).sum

/-- `totalMoves` is `tm` for the queen directions. -/
private lemma totalMoves_eq (n : ℕ) (S : Finset (ℕ × ℕ)) :
    totalMoves n S = tm queenDirs n S := rfl

/-- The embedding of `ℕ × ℕ` into `ℤ × ℤ`. -/
private def emb : ℕ × ℕ ↪ ℤ × ℤ :=
  ⟨fun p => ((p.1 : ℤ), (p.2 : ℤ)), fun a b h => by
    simp only [Prod.mk.injEq, Nat.cast_inj] at h; exact Prod.ext h.1 h.2⟩

@[simp] private lemma emb_apply (p : ℕ × ℕ) : emb p = ((p.1 : ℤ), (p.2 : ℤ)) := rfl

/-- The board as a set of integer points. -/
private def BZ (n : ℕ) : Finset (ℤ × ℤ) := (board n).map emb

/-- A placement as a set of integer points. -/
private def SZ (S : Finset (ℕ × ℕ)) : Finset (ℤ × ℤ) := S.map emb

/-- Membership in the integer board. -/
private lemma mem_BZ {n : ℕ} {c : ℤ × ℤ} :
    c ∈ BZ n ↔ 0 ≤ c.1 ∧ c.1 < n ∧ 0 ≤ c.2 ∧ c.2 < n := by
  constructor
  · intro h
    simp only [BZ, Finset.mem_map, board, Finset.mem_product, Finset.mem_range] at h
    obtain ⟨p, ⟨h1, h2⟩, rfl⟩ := h
    simp only [emb_apply]
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    simp only [BZ, Finset.mem_map, board, Finset.mem_product, Finset.mem_range]
    refine ⟨(c.1.toNat, c.2.toNat), ⟨by omega, by omega⟩, ?_⟩
    simp only [emb_apply]
    ext <;> simp <;> omega

/-- Membership in the integer placement, for nonnegative points. -/
private lemma mem_SZ {S : Finset (ℕ × ℕ)} {c : ℤ × ℤ} (h1 : 0 ≤ c.1) (h2 : 0 ≤ c.2) :
    c ∈ SZ S ↔ (c.1.toNat, c.2.toNat) ∈ S := by
  constructor
  · intro h
    simp only [SZ, Finset.mem_map] at h
    obtain ⟨p, hp, rfl⟩ := h
    simpa using hp
  · intro h
    simp only [SZ, Finset.mem_map]
    refine ⟨_, h, ?_⟩
    simp only [emb_apply]
    ext <;> simp <;> omega

/-- A placement on the board stays on the board as a set of integer points. -/
private lemma SZ_sub_BZ {n : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ board n) : SZ S ⊆ BZ n :=
  Finset.map_subset_map.mpr hS

/-- The empty squares of the board. -/
private abbrev E (n : ℕ) (S : Finset (ℕ × ℕ)) (c : ℤ × ℤ) : Prop := c ∈ BZ n ∧ c ∉ SZ S

/-- `isEmptySquare` in terms of `BZ` and `SZ`. -/
private lemma isEmpty_iff {n : ℕ} {S : Finset (ℕ × ℕ)} {x y : ℤ} :
    isEmptySquare n S x y = true ↔ E n S (x, y) := by
  simp only [isEmptySquare, decide_eq_true_eq, E, mem_BZ]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h3, h4⟩, fun h => h5 ((mem_SZ h1 h3).mp h)⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, fun h => h5 ((mem_SZ h1 h3).mpr h)⟩

/-- Length of `takeWhile` on `range'` as a count of good prefixes. -/
private lemma tw_len (P : ℕ → Bool) (m s : ℕ) :
    ((List.range' s m).takeWhile P).length =
      ∑ k ∈ Finset.range m, if (∀ j < k + 1, P (s + j) = true) then 1 else 0 := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    rw [List.range'_succ, List.takeWhile_cons, Finset.sum_range_succ']
    by_cases hs : P s = true
    · have h0 : (∀ j < 0 + 1, P (s + j) = true) := by
        intro j hj; obtain rfl : j = 0 := by omega
        simpa using hs
      rw [if_pos hs, List.length_cons, ih (s + 1), if_pos h0]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      apply if_congr _ rfl rfl
      constructor
      · intro h j hj
        rcases j with _ | j
        · simpa using hs
        · have := h j (by omega); rwa [show s + 1 + j = s + (j + 1) by ring] at this
      · intro h j hj; have := h (j + 1) (by omega); rwa [show s + (j + 1) = s + 1 + j by ring] at this
    · have h0 : ¬ (∀ j < 0 + 1, P (s + j) = true) := fun h => hs (by simpa using h 0 (by omega))
      rw [if_neg hs, if_neg h0, List.length_nil, add_zero]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg]
      intro h; exact hs (by simpa using h 0 (by omega))

/-- The point `c + t • d`. -/
private def sh (c d : ℤ × ℤ) (t : ℤ) : ℤ × ℤ := (c.1 + t * d.1, c.2 + t * d.2)

/-- The coercion of a list of naturals to a list of integers is a `map`. -/
private lemma bind_pure_cast (l : List ℕ) :
    (l >>= fun (a : ℕ) => (pure (a : ℤ) : List ℤ)) = l.map (fun a : ℕ => (a : ℤ)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp_all

/-- `rayMoves` counts the `k < n` such that the first `k + 1` squares of the ray are empty. -/
private lemma rayMoves_eq (n : ℕ) (S : Finset (ℕ × ℕ)) (p : ℕ × ℕ) (d : ℤ × ℤ) :
    rayMoves n S p d = ∑ k ∈ Finset.range n,
      if (∀ j < k + 1, E n S (sh (emb p) d (1 + j))) then 1 else 0 := by
  rw [rayMoves, bind_pure_cast, List.takeWhile_map, List.length_map, tw_len]
  apply Finset.sum_congr rfl
  intro k _
  apply if_congr _ rfl rfl
  apply forall_congr'; intro j; apply imp_congr_right; intro _
  simp only [Function.comp_apply, isEmpty_iff, sh, emb_apply]
  push_cast
  rfl

/-- `Y n S d c = 1` iff `c` is an empty square reached by a piece moving in direction `d`. -/
private def Y (n : ℕ) (S : Finset (ℕ × ℕ)) (d c : ℤ × ℤ) : ℕ :=
  ∑ k ∈ Finset.range n,
    if (sh c d (-(k + 1)) ∈ SZ S ∧ ∀ j < k + 1, E n S (sh c d (-j))) then 1 else 0

/-- Composition of shifts along `d`. -/
private lemma sh_sh (c d : ℤ × ℤ) (s t : ℤ) : sh (sh c d s) d t = sh c d (s + t) := by
  simp only [sh]; ext <;> simp <;> ring

/-- The zero shift. -/
private lemma sh_zero (c d : ℤ × ℤ) : sh c d 0 = c := by simp [sh]

/-- Double counting: total moves in direction `d` = number of reached empty squares. -/
private lemma sum_ray_eq (n : ℕ) (S : Finset (ℕ × ℕ)) (d : ℤ × ℤ) :
    ∑ p ∈ S, rayMoves n S p d = ∑ c ∈ BZ n, Y n S d c := by
  simp only [rayMoves_eq, Y]
  rw [← Finset.sum_map S emb (fun q => ∑ k ∈ Finset.range n,
      if (∀ j < k + 1, E n S (sh q d (1 + j))) then 1 else 0)]
  rw [Finset.sum_comm, Finset.sum_comm (s := BZ n)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_bij_ne_zero (fun q _ _ => sh q d (k + 1))
  · intro q hq hne
    have h := (by simpa using hne : ∀ j < k + 1, E n S (sh q d (1 + j)))
    have := (h k (by omega)).1
    rwa [show (1 : ℤ) + (k : ℕ) = (k : ℤ) + 1 by ring] at this
  · intro q1 _ _ q2 _ _ h
    have := congrArg (fun c => sh c d (-(k + 1))) h
    simpa [sh_sh, sh_zero] using this
  · intro c hc hne
    have h := (by simpa using hne : sh c d (-(k + 1)) ∈ SZ S ∧
      ∀ j < k + 1, E n S (sh c d (-j)))
    refine ⟨sh c d (-(k + 1)), h.1, ?_, by simp [sh_sh, sh_zero]⟩
    rw [if_pos]
    · exact one_ne_zero
    intro j hj
    have := h.2 (k - j) (by omega)
    rw [sh_sh]
    convert this using 2
    push_cast [Nat.cast_sub (by omega : j ≤ k)]
    ring
  · intro q hq _
    apply if_congr _ rfl rfl
    rw [sh_sh, show ((k : ℤ) + 1 + -(k + 1)) = 0 by ring, sh_zero]
    have hq' : q ∈ SZ S := hq
    simp only [hq', true_and]
    constructor
    · intro h j hj
      have := h (k - j) (by omega)
      rw [sh_sh]
      convert this using 2
      push_cast [Nat.cast_sub (by omega : j ≤ k)]
      ring
    · intro h j hj
      have := h (k - j) (by omega)
      rw [sh_sh] at this
      convert this using 2
      push_cast [Nat.cast_sub (by omega : j ≤ k)]
      ring


/-! ### The dual (flow) inequality -/

/-- Occupancy indicator. -/
private def X (S : Finset (ℕ × ℕ)) (c : ℤ × ℤ) : ℤ := if c ∈ SZ S then 1 else 0

/-- At most one piece reaches a given square in a given direction. -/
private lemma Y_le_one (n : ℕ) (S : Finset (ℕ × ℕ)) (d c : ℤ × ℤ) : Y n S d c ≤ 1 := by
  unfold Y
  rw [Finset.sum_boole]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  by_contra hab
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact (hb.2.2 (a + 1) (by omega)).2 (by simpa using ha.2.1)
  · exact (ha.2.2 (b + 1) (by omega)).2 (by simpa using hb.2.1)

/-- Only empty squares of the board are reached. -/
private lemma Y_eq_zero_of_not_E {n : ℕ} {S : Finset (ℕ × ℕ)} {d c : ℤ × ℤ} (h : ¬ E n S c) :
    Y n S d c = 0 := by
  unfold Y
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg]
  rintro ⟨_, h2⟩
  exact h (by simpa [sh_zero] using h2 0 (by omega))

/-- `Y c ≤ x (c - d) + Y (c - d)`: the square behind `c` is a piece or is itself reached. -/
private lemma Y_rec (n : ℕ) (S : Finset (ℕ × ℕ)) (d c : ℤ × ℤ) :
    (Y n S d c : ℤ) ≤ X S (sh c d (-1)) + Y n S d (sh c d (-1)) := by
  rcases Nat.eq_zero_or_pos (Y n S d c) with h | h
  · rw [h]; unfold X; split_ifs <;> positivity
  have h1 : Y n S d c = 1 := le_antisymm (Y_le_one n S d c) h
  rw [h1]
  unfold Y at h
  obtain ⟨k, hk, hk2⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp h)
  rw [Finset.mem_range] at hk
  have hk3 : sh c d (-(k + 1)) ∈ SZ S ∧ ∀ j < k + 1, E n S (sh c d (-j)) := by
    by_contra hc; exact hk2 (if_neg hc)
  rcases k with _ | k
  · have : X S (sh c d (-1)) = 1 := by
      unfold X; rw [if_pos]; simpa using hk3.1
    rw [this]; push_cast; omega
  · have hY : 1 ≤ Y n S d (sh c d (-1)) := by
      unfold Y
      have hsub : ({k} : Finset ℕ) ⊆ Finset.range n := by
        intro x hx; rw [Finset.mem_singleton] at hx; subst hx; rw [Finset.mem_range]; omega
      calc 1 = ∑ k' ∈ ({k} : Finset ℕ), (if (sh (sh c d (-1)) d (-(k' + 1)) ∈ SZ S ∧
            ∀ j < k' + 1, E n S (sh (sh c d (-1)) d (-j))) then 1 else 0) := by
              rw [Finset.sum_singleton, if_pos]
              refine ⟨?_, ?_⟩
              · rw [sh_sh]; convert hk3.1 using 2; push_cast; ring
              · intro j hj; rw [sh_sh]
                convert hk3.2 (j + 1) (by omega) using 2; push_cast; ring
        _ ≤ _ := Finset.sum_le_sum_of_subset hsub
    have : 0 ≤ X S (sh c d (-1)) := by unfold X; split_ifs <;> norm_num
    push_cast; omega

/-- Squares whose predecessor in direction `d` is off the board are not reached. -/
private lemma Y_first {n : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ board n) {d c : ℤ × ℤ} (hd : sh c d (-1) ∉ BZ n) : Y n S d c = 0 := by
  unfold Y
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rcases k with _ | k
  · exact hd (SZ_sub_BZ hS (by simpa using h1))
  · exact hd (by simpa using (h2 1 (by omega)).1)

/-- Shifting a sum along the direction `d`. -/
private lemma shift_sum (n : ℕ) (d : ℤ × ℤ) (f g : ℤ × ℤ → ℤ)
    (hf : ∀ c, f c ≠ 0 → c ∈ BZ n ∧ sh c d (-1) ∈ BZ n) :
    ∑ c ∈ BZ n, f (sh c d 1) * g c = ∑ c ∈ BZ n, f c * g (sh c d (-1)) := by
  apply Finset.sum_bij_ne_zero (fun c _ _ => sh c d 1)
  · intro c _ h
    exact (hf _ (left_ne_zero_of_mul h)).1
  · intro a _ _ b _ _ h
    have := congrArg (fun c => sh c d (-1)) h
    simpa [sh_sh, sh_zero] using this
  · intro c _ h
    have h2 := hf _ (left_ne_zero_of_mul h)
    refine ⟨sh c d (-1), h2.2, ?_, by simp [sh_sh, sh_zero]⟩
    rw [sh_sh, show (-1 : ℤ) + 1 = 0 by ring, sh_zero]
    exact h
  · intro c _ _
    rw [sh_sh, show (1 : ℤ) + -1 = 0 by ring, sh_zero]

/-- The flow inequality for one direction. -/
private lemma dir_ineq {n : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ board n) (D : ℤ) (d : ℤ × ℤ)
    (G : ℤ × ℤ → ℤ) (h0 : ∀ c, 0 ≤ G c)
    (hsupp : ∀ c, G c ≠ 0 → c ∈ BZ n ∧ sh c d (-1) ∈ BZ n)
    (hα : ∀ c ∈ BZ n, sh c d (-1) ∈ BZ n → G c ≤ D + G (sh c d 1)) :
    D * (∑ p ∈ S, rayMoves n S p d : ℕ) ≤
      ∑ c ∈ BZ n, ((if sh c d (-1) ∈ BZ n then D + G (sh c d 1) - G c else 0) * (1 - X S c)
        + G (sh c d 1) * X S c) := by
  rw [sum_ray_eq]
  have hX0 : ∀ c, 0 ≤ X S c := fun c => by unfold X; split_ifs <;> norm_num
  have hX1 : ∀ c, X S c ≤ 1 := fun c => by unfold X; split_ifs <;> norm_num
  -- the per-cell inequality
  have hcell : ∀ c ∈ BZ n, D * (Y n S d c : ℤ) + G (sh c d 1) * Y n S d c ≤
      (if sh c d (-1) ∈ BZ n then D + G (sh c d 1) - G c else 0) * (1 - X S c) +
        G c * X S (sh c d (-1)) + G c * Y n S d (sh c d (-1)) := by
    intro c hc
    have hY1 := Y_le_one n S d c
    have hYr := Y_rec n S d c
    have hG := h0 c
    have hX := hX0 (sh c d (-1))
    have hYc : (0 : ℤ) ≤ Y n S d (sh c d (-1)) := by positivity
    by_cases hd : sh c d (-1) ∈ BZ n
    · rw [if_pos hd]
      have ha := hα c hc hd
      rcases Nat.eq_zero_or_pos (Y n S d c) with h | h
      · rw [h]; push_cast
        have := hX1 c
        nlinarith
      · have h1 : Y n S d c = 1 := le_antisymm hY1 h
        have hxc : X S c = 0 := by
          unfold X; rw [if_neg]; intro hm
          have := Y_eq_zero_of_not_E (n := n) (d := d) (fun hE => hE.2 hm)
          omega
        rw [h1, hxc] at *; push_cast at *
        nlinarith
    · rw [if_neg hd, Y_first hS hd]
      push_cast
      nlinarith
  have hsum := Finset.sum_le_sum hcell
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have e1 := shift_sum n d G (fun c => (Y n S d c : ℤ)) hsupp
  have e2 := shift_sum n d G (X S) hsupp
  push_cast
  rw [Finset.mul_sum, Finset.sum_add_distrib]
  linarith


/-- The "empty" weight of a cell. -/
private def Af (n : ℕ) (D : ℤ) (dirs : List (ℤ × ℤ)) (G : ℤ × ℤ → ℤ × ℤ → ℤ) (c : ℤ × ℤ) : ℤ :=
  (dirs.map fun d => if sh c d (-1) ∈ BZ n then D + G d (sh c d 1) - G d c else 0).sum

/-- The "occupied" weight of a cell. -/
private def Bf (dirs : List (ℤ × ℤ)) (G : ℤ × ℤ → ℤ × ℤ → ℤ) (c : ℤ × ℤ) : ℤ :=
  (dirs.map fun d => G d (sh c d 1)).sum

/-- The main inequality: weighted total moves are bounded by the cell weights. -/
private theorem key {n : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ board n) (D : ℤ)
    (dirs : List (ℤ × ℤ)) (G : ℤ × ℤ → ℤ × ℤ → ℤ) (h0 : ∀ d c, 0 ≤ G d c)
    (hsupp : ∀ d c, G d c ≠ 0 → c ∈ BZ n ∧ sh c d (-1) ∈ BZ n)
    (hα : ∀ d ∈ dirs, ∀ c ∈ BZ n, sh c d (-1) ∈ BZ n → G d c ≤ D + G d (sh c d 1)) :
    D * (tm dirs n S : ℤ) ≤
      ∑ c ∈ BZ n, (if c ∈ SZ S then Bf dirs G c else Af n D dirs G c) := by
  have main : ∀ L : List (ℤ × ℤ), (∀ d ∈ L, ∀ c ∈ BZ n, sh c d (-1) ∈ BZ n →
      G d c ≤ D + G d (sh c d 1)) →
      D * (∑ p ∈ S, (L.map (rayMoves n S p)).sum : ℕ) ≤
        ∑ c ∈ BZ n, ((1 - X S c) * Af n D L G c + X S c * Bf L G c) := by
    intro L
    induction L with
    | nil => intro _; simp [Af, Bf]
    | cons d L ih =>
      intro hL
      have h1 := dir_ineq hS D d (G d) (h0 d) (hsupp d) (hL d (by simp))
      have h2 := ih (fun d' hd' => hL d' (by simp [hd']))
      have e : ∀ p ∈ S, ((d :: L).map (rayMoves n S p)).sum =
          rayMoves n S p d + (L.map (rayMoves n S p)).sum := by intro p _; simp
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
      have e2 : ∀ c ∈ BZ n, (1 - X S c) * Af n D (d :: L) G c + X S c * Bf (d :: L) G c =
          ((if sh c d (-1) ∈ BZ n then D + G d (sh c d 1) - G d c else 0) * (1 - X S c) +
            G d (sh c d 1) * X S c) + ((1 - X S c) * Af n D L G c + X S c * Bf L G c) := by
        intro c _; simp only [Af, Bf, List.map_cons, List.sum_cons]; ring
      rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib]
      push_cast at h1 h2 ⊢
      linarith
  have hm := main dirs hα
  have htot : tm dirs n S = ∑ p ∈ S, (dirs.map (rayMoves n S p)).sum := rfl
  rw [htot]
  refine hm.trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
  unfold X
  split_ifs <;> ring


/-! ### Checking certificates by computation -/

/-- Board membership as a boolean. -/
private def inB (n : ℕ) (c : ℤ × ℤ) : Bool := decide (0 ≤ c.1 ∧ c.1 < n ∧ 0 ≤ c.2 ∧ c.2 < n)

/-- `inB` decides board membership. -/
private lemma inB_iff {n : ℕ} {c : ℤ × ℤ} : inB n c = true ↔ c ∈ BZ n := by
  simp [inB, mem_BZ]

/-- A flow given by a table of natural numbers, cut off outside the board. -/
private def Gt (n : ℕ) (T : ℤ × ℤ → ℤ × ℤ → ℕ) (d c : ℤ × ℤ) : ℤ :=
  if inB n c && inB n (sh c d (-1)) then (T d c : ℤ) else 0

/-- Table lookup: entries `(d₁, d₂, i, j, v)`. -/
private def tab (L : List (ℤ × ℤ × ℤ × ℤ × ℕ)) (d c : ℤ × ℤ) : ℕ :=
  match L.find? (fun e => e.1 == d.1 && e.2.1 == d.2 && e.2.2.1 == c.1 && e.2.2.2.1 == c.2) with
  | some e => e.2.2.2.2
  | none => 0

/-- Computable version of `Af`. -/
private def Afc (n : ℕ) (D : ℤ) (dirs : List (ℤ × ℤ)) (G : ℤ × ℤ → ℤ × ℤ → ℤ) (c : ℤ × ℤ) : ℤ :=
  (dirs.map fun d => if inB n (sh c d (-1)) then D + G d (sh c d 1) - G d c else 0).sum

/-- `Af` agrees with its computable version. -/
private lemma Af_eq (n : ℕ) (D : ℤ) (dirs : List (ℤ × ℤ)) (G : ℤ × ℤ → ℤ × ℤ → ℤ) (c : ℤ × ℤ) :
    Af n D dirs G c = Afc n D dirs G c := by
  unfold Af Afc
  congr 1
  apply List.map_congr_left
  intro d _
  by_cases h : sh c d (-1) ∈ BZ n
  · rw [if_pos h, if_pos (inB_iff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (inB_iff.mp h'))]

/-- The `α ≥ 0` condition, checked cell by cell. -/
private def checkA (n : ℕ) (D : ℤ) (dirs : List (ℤ × ℤ)) (G : ℤ × ℤ → ℤ × ℤ → ℤ) : Bool :=
  dirs.all fun d => (List.range n).all fun i => (List.range n).all fun j =>
    !inB n (sh ((i : ℤ), (j : ℤ)) d (-1)) || decide (G d ((i : ℤ), (j : ℤ)) ≤
      D + G d (sh ((i : ℤ), (j : ℤ)) d 1))

/-- The bound for one cell, given cells known to be occupied (`In`) or empty (`Out`). -/
private def bnd (n : ℕ) (D : ℤ) (dirs : List (ℤ × ℤ)) (G : ℤ × ℤ → ℤ × ℤ → ℤ)
    (In Out : List (ℕ × ℕ)) (i j : ℕ) : ℤ :=
  if (i, j) ∈ In then Bf dirs G ((i : ℤ), (j : ℤ))
  else if (i, j) ∈ Out then Afc n D dirs G ((i : ℤ), (j : ℤ))
  else max (Afc n D dirs G ((i : ℤ), (j : ℤ))) (Bf dirs G ((i : ℤ), (j : ℤ)))

/-- The total of the cell bounds. -/
private def bndSum (n : ℕ) (D : ℤ) (dirs : List (ℤ × ℤ)) (G : ℤ × ℤ → ℤ × ℤ → ℤ)
    (In Out : List (ℕ × ℕ)) : ℤ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, bnd n D dirs G In Out i j

/-- Sums over the integer board as double sums over `range n`. -/
private lemma sum_BZ (n : ℕ) (f : ℤ × ℤ → ℤ) :
    ∑ c ∈ BZ n, f c = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f ((i : ℤ), (j : ℤ)) := by
  rw [BZ, Finset.sum_map, board, Finset.sum_product]
  rfl

/-- A leaf certificate bounds the total number of moves. -/
private theorem leaf {n : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ board n) (D : ℤ) (hD : 0 < D)
    (dirs : List (ℤ × ℤ)) (T : ℤ × ℤ → ℤ × ℤ → ℕ) (In Out : List (ℕ × ℕ)) (target : ℕ)
    (h1 : checkA n D dirs (Gt n T) = true)
    (h2 : bndSum n D dirs (Gt n T) In Out < D * (target + 1))
    (hIn : ∀ p ∈ In, p ∈ S) (hOut : ∀ p ∈ Out, p ∉ S) :
    tm dirs n S ≤ target := by
  have hk := key hS D dirs (Gt n T)
    (fun d c => by unfold Gt; split_ifs <;> positivity)
    (fun d c h => by
      unfold Gt at h
      split_ifs at h with hc
      · simp only [Bool.and_eq_true] at hc
        exact ⟨inB_iff.mp hc.1, inB_iff.mp hc.2⟩
      · exact absurd rfl h)
    (fun d hd c hc hc' => by
      have h1' := h1
      unfold checkA at h1'
      rw [List.all_eq_true] at h1'
      have h3 := h1' d hd
      rw [mem_BZ] at hc
      obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = c.1 := ⟨c.1.toNat, by omega⟩
      obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = c.2 := ⟨c.2.toNat, by omega⟩
      rw [List.all_eq_true] at h3
      have h4 := h3 i (List.mem_range.mpr (by omega))
      rw [List.all_eq_true] at h4
      have h5 := h4 j (List.mem_range.mpr (by omega))
      have hc2 : c = ((i : ℤ), (j : ℤ)) := by ext <;> simp [hi, hj]
      subst hc2
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h5
      rcases h5 with h5 | h5
      · exact absurd (inB_iff.mpr hc') (by simp [h5])
      · exact h5)
  have hle : ∑ c ∈ BZ n, (if c ∈ SZ S then Bf dirs (Gt n T) c else Af n D dirs (Gt n T) c) ≤
      bndSum n D dirs (Gt n T) In Out := by
    rw [sum_BZ, bndSum]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    have hmem : ((i : ℤ), (j : ℤ)) ∈ SZ S ↔ (i, j) ∈ S := by
      rw [mem_SZ (by simp) (by simp)]; simp
    rw [Af_eq, bnd]
    by_cases hI : (i, j) ∈ In
    · rw [if_pos (hmem.mpr (hIn _ hI)), if_pos hI]
    · rw [if_neg hI]
      by_cases hO : (i, j) ∈ Out
      · rw [if_neg (fun h => hOut _ hO (hmem.mp h)), if_pos hO]
      · rw [if_neg hO]
        split_ifs
        · exact le_max_right _ _
        · exact le_max_left _ _
  have : D * (tm dirs n S : ℤ) < D * (target + 1) := by linarith
  have := lt_of_mul_lt_mul_left this hD.le
  omega


/-! ### The general case: flows depending only on the position class of a cell -/

/-- Position class of a coordinate, cut off at `3`: `0, 1, 2` near the start, `3` in the
middle, `4, 5, 6` near the end. -/
private def cls3 (n : ℕ) (x : ℤ) : ℕ :=
  if x < 3 then x.toNat else if (n : ℤ) - 1 - x < 3 then (6 - ((n : ℤ) - 1 - x)).toNat else 3

/-- Position class of a coordinate, cut off at `4`: `0, …, 3` near the start, `4` in the
middle, `5, …, 8` near the end. -/
private def cls4 (n : ℕ) (x : ℤ) : ℕ :=
  if x < 4 then x.toNat else if (n : ℤ) - 1 - x < 4 then (8 - ((n : ℤ) - 1 - x)).toNat else 4

/-- Whether a step `δ` from a coordinate of class `v` stays on the board. -/
private def ok4 (v : ℕ) (δ : ℤ) : Bool := !(v == 0 && δ == -1) && !(v == 8 && δ == 1)

/-- The `cls3` class after a step `δ` from a coordinate of `cls4` class `v`. -/
private def sh3 (v : ℕ) (δ : ℤ) : ℕ :=
  if v ≤ 3 then (if (v : ℤ) + δ < 3 then ((v : ℤ) + δ).toNat else 3)
  else if v = 4 then 3
  else (if 8 - (v : ℤ) - δ < 3 then ((v : ℤ) + δ - 2).toNat else 3)

/-- Classes with cut-off `4` are at most `8`. -/
private lemma cls4_le (n : ℕ) (x : ℤ) (hx : 0 ≤ x) (hxn : x < n) : cls4 n x ≤ 8 := by
  unfold cls4; split_ifs <;> omega

/-- `ok4` decides whether a step stays on the board (for `n ≥ 8`). -/
private lemma ok4_iff {n : ℕ} (hn : 8 ≤ n) {x δ : ℤ} (hx : 0 ≤ x) (hxn : x < n)
    (hδ : -1 ≤ δ ∧ δ ≤ 1) : ok4 (cls4 n x) δ = true ↔ 0 ≤ x + δ ∧ x + δ < n := by
  unfold ok4 cls4
  split_ifs with h1 h2 <;> simp <;> omega

/-- The `cls3` class after a step is determined by the `cls4` class before it (`n ≥ 8`). -/
private lemma cls3_shift {n : ℕ} (hn : 8 ≤ n) {x δ : ℤ} (hx : 0 ≤ x) (hxn : x < n)
    (hδ : -1 ≤ δ ∧ δ ≤ 1) (h1 : 0 ≤ x + δ) (h2 : x + δ < n) :
    cls3 n (x + δ) = sh3 (cls4 n x) δ := by
  unfold cls3 sh3 cls4
  split_ifs <;> omega

/-- Lookup in a class table: entries `(u, w, d₁, d₂, v)`. -/
private def tabC (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) (u w : ℕ) (d : ℤ × ℤ) : ℕ :=
  match L.find? (fun e => e.1 == u && e.2.1 == w && e.2.2.1 == d.1 && e.2.2.2.1 == d.2) with
  | some e => e.2.2.2.2
  | none => 0

/-- The flow defined by a class table. -/
private def Gc (n : ℕ) (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) : ℤ × ℤ → ℤ × ℤ → ℤ :=
  Gt n (fun d c => tabC L (cls3 n c.1) (cls3 n c.2) d)

/-- Flow into the cell `c` from `c + d`, by classes. -/
private def G1 (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) (v w : ℕ) (d : ℤ × ℤ) : ℤ :=
  if ok4 v d.1 && ok4 w d.2 then (tabC L (sh3 v d.1) (sh3 w d.2) d : ℤ) else 0

/-- Flow out of the cell `c`, by classes. -/
private def G0 (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) (v w : ℕ) (d : ℤ × ℤ) : ℤ :=
  (tabC L (sh3 v 0) (sh3 w 0) d : ℤ)

/-- `Af` by classes. -/
private def Aty (D : ℤ) (dirs : List (ℤ × ℤ)) (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) (v w : ℕ) : ℤ :=
  (dirs.map fun d => if ok4 v (-d.1) && ok4 w (-d.2) then D + G1 L v w d - G0 L v w d
    else 0).sum

/-- `Bf` by classes. -/
private def Bty (dirs : List (ℤ × ℤ)) (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) (v w : ℕ) : ℤ :=
  (dirs.map fun d => G1 L v w d).sum

/-- The cell bound by classes. -/
private def Mty (D : ℤ) (dirs : List (ℤ × ℤ)) (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) (v w : ℕ) : ℤ :=
  max (Aty D dirs L v w) (Bty dirs L v w)

/-- Unit directions. -/
private def unitDir (d : ℤ × ℤ) : Prop := -1 ≤ d.1 ∧ d.1 ≤ 1 ∧ -1 ≤ d.2 ∧ d.2 ≤ 1

/-- Board membership of a neighbour, by classes. -/
private lemma memBZ_shift {n : ℕ} (hn : 8 ≤ n) {c d : ℤ × ℤ} (hc : c ∈ BZ n) (hd : unitDir d)
    (s : ℤ) (hs : s = 1 ∨ s = -1) :
    sh c d s ∈ BZ n ↔ (ok4 (cls4 n c.1) (s * d.1) && ok4 (cls4 n c.2) (s * d.2)) = true := by
  rw [mem_BZ] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  obtain ⟨d1, d2, d3, d4⟩ := hd
  have hδ1 : -1 ≤ s * d.1 ∧ s * d.1 ≤ 1 := by rcases hs with rfl | rfl <;> constructor <;> linarith
  have hδ2 : -1 ≤ s * d.2 ∧ s * d.2 ≤ 1 := by rcases hs with rfl | rfl <;> constructor <;> linarith
  rw [Bool.and_eq_true, ok4_iff hn h1 h2 hδ1, ok4_iff hn h3 h4 hδ2, mem_BZ]
  simp only [sh]
  constructor
  · rintro ⟨a, b, c, e⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨a, b⟩, ⟨c, e⟩⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The flow at `c + d`, by classes. -/
private lemma Gc_one {n : ℕ} (hn : 8 ≤ n) (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) {c d : ℤ × ℤ}
    (hc : c ∈ BZ n) (hd : unitDir d) :
    Gc n L d (sh c d 1) = G1 L (cls4 n c.1) (cls4 n c.2) d := by
  have hm := memBZ_shift hn hc hd 1 (Or.inl rfl)
  simp only [one_mul] at hm
  unfold Gc Gt G1
  have hback : sh (sh c d 1) d (-1) = c := by
    rw [sh_sh, show (1 : ℤ) + -1 = 0 by ring, sh_zero]
  rw [hback, inB_iff.mpr hc, Bool.and_true]
  by_cases h : sh c d 1 ∈ BZ n
  · rw [if_pos (inB_iff.mpr h), if_pos (hm.mp h)]
    rw [mem_BZ] at hc
    obtain ⟨d1, d2, d3, d4⟩ := hd
    have h' := mem_BZ.mp h
    simp only [sh, one_mul] at h' ⊢
    rw [cls3_shift hn hc.1 hc.2.1 ⟨d1, d2⟩ (by linarith) (by linarith),
      cls3_shift hn hc.2.2.1 hc.2.2.2 ⟨d3, d4⟩ (by linarith) (by linarith)]
  · rw [if_neg (fun h' => h (inB_iff.mp h')), if_neg (fun h' => h (hm.mpr h'))]

/-- The flow at `c` (when `c - d` is on the board), by classes. -/
private lemma Gc_zero {n : ℕ} (hn : 8 ≤ n) (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) {c d : ℤ × ℤ}
    (hc : c ∈ BZ n) (hd' : sh c d (-1) ∈ BZ n) :
    Gc n L d c = G0 L (cls4 n c.1) (cls4 n c.2) d := by
  unfold Gc Gt G0
  rw [inB_iff.mpr hc, inB_iff.mpr hd', Bool.and_self, if_pos rfl]
  rw [mem_BZ] at hc
  have e1 := cls3_shift hn hc.1 hc.2.1 ⟨by norm_num, by norm_num⟩ (by linarith) (by linarith)
    (δ := 0)
  have e2 := cls3_shift hn hc.2.2.1 hc.2.2.2 ⟨by norm_num, by norm_num⟩ (by linarith)
    (by linarith) (δ := 0)
  simp only [add_zero] at e1 e2
  dsimp only
  rw [e1, e2]

/-- `Af` depends only on the classes of the coordinates. -/
private lemma Af_ty {n : ℕ} (hn : 8 ≤ n) (D : ℤ) (dirs : List (ℤ × ℤ))
    (hdirs : ∀ d ∈ dirs, unitDir d) (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) {c : ℤ × ℤ}
    (hc : c ∈ BZ n) : Af n D dirs (Gc n L) c = Aty D dirs L (cls4 n c.1) (cls4 n c.2) := by
  unfold Af Aty
  congr 1
  apply List.map_congr_left
  intro d hd
  have hm := memBZ_shift hn hc (hdirs d hd) (-1) (Or.inr rfl)
  simp only [neg_one_mul] at hm
  by_cases h : sh c d (-1) ∈ BZ n
  · rw [if_pos h, if_pos (hm.mp h), Gc_one hn L hc (hdirs d hd), Gc_zero hn L hc h]
  · rw [if_neg h, if_neg (fun h' => h (hm.mpr h'))]

/-- `Bf` depends only on the classes of the coordinates. -/
private lemma Bf_ty {n : ℕ} (hn : 8 ≤ n) (dirs : List (ℤ × ℤ))
    (hdirs : ∀ d ∈ dirs, unitDir d) (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) {c : ℤ × ℤ}
    (hc : c ∈ BZ n) : Bf dirs (Gc n L) c = Bty dirs L (cls4 n c.1) (cls4 n c.2) := by
  unfold Bf Bty
  congr 1
  apply List.map_congr_left
  intro d hd
  rw [Gc_one hn L hc (hdirs d hd)]

/-- The `α ≥ 0` condition by classes. -/
private def checkTy (D : ℤ) (dirs : List (ℤ × ℤ)) (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) : Bool :=
  dirs.all fun d => (List.range 9).all fun v => (List.range 9).all fun w =>
    !(ok4 v (-d.1) && ok4 w (-d.2)) || decide (G0 L v w d ≤ D + G1 L v w d)

/-- The eight boundary classes. -/
private def E8 : Finset ℕ := {0, 1, 2, 3, 5, 6, 7, 8}

/-- Summing a function of the class over a coordinate, for `n ≥ 8`. -/
private lemma sum_cls4 {n : ℕ} (hn : 8 ≤ n) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range n, f (cls4 n i) = ∑ v ∈ E8, f v + ((n : ℤ) - 8) * f 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m + 4 := ⟨n - 8, by omega⟩
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have hmid : ∀ x ∈ Finset.range m, f (cls4 (4 + m + 4) ((4 + x : ℕ) : ℤ)) = f 4 := by
    intro x hx
    rw [Finset.mem_range] at hx
    congr 1
    unfold cls4; push_cast; split_ifs <;> omega
  rw [Finset.sum_congr rfl hmid, Finset.sum_const, Finset.card_range]
  have hv : ∀ k : ℕ, k < 4 → cls4 (4 + m + 4) (k : ℤ) = k := by
    intro k hk; unfold cls4; push_cast; split_ifs <;> omega
  have hw : ∀ k : ℕ, k < 4 → cls4 (4 + m + 4) ((4 + m + k : ℕ) : ℤ) = 5 + k := by
    intro k hk; unfold cls4; push_cast; split_ifs <;> omega
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hv 0 (by norm_num), hv 1 (by norm_num), hv 2 (by norm_num), hv 3 (by norm_num),
    hw 0 (by norm_num), hw 1 (by norm_num), hw 2 (by norm_num), hw 3 (by norm_num)]
  simp only [E8]
  norm_num
  ring

/-- The general bound for `n ≥ 8`. -/
private theorem general {n : ℕ} (hn : 8 ≤ n) {S : Finset (ℕ × ℕ)} (hS : S ⊆ board n) (D : ℤ)
    (hD : 0 < D) (dirs : List (ℤ × ℤ)) (hdirs : ∀ d ∈ dirs, unitDir d)
    (L : List (ℕ × ℕ × ℤ × ℤ × ℕ)) (hchk : checkTy D dirs L = true) (target : ℕ)
    (htarget : ∑ v ∈ E8, ∑ w ∈ E8, Mty D dirs L v w +
      ((n : ℤ) - 8) * (∑ v ∈ E8, Mty D dirs L v 4 + ∑ w ∈ E8, Mty D dirs L 4 w) +
      ((n : ℤ) - 8) * ((n : ℤ) - 8) * Mty D dirs L 4 4 = D * target) :
    tm dirs n S ≤ target := by
  have hk := key hS D dirs (Gc n L)
    (fun d c => by unfold Gc Gt; split_ifs <;> positivity)
    (fun d c h => by
      unfold Gc Gt at h
      split_ifs at h with hc
      · simp only [Bool.and_eq_true] at hc
        exact ⟨inB_iff.mp hc.1, inB_iff.mp hc.2⟩
      · exact absurd rfl h)
    (fun d hd c hc hc' => by
      rw [Gc_one hn L hc (hdirs d hd), Gc_zero hn L hc hc']
      have h1 := hchk
      unfold checkTy at h1
      rw [List.all_eq_true] at h1
      have h3 := h1 d hd
      have hm := (memBZ_shift hn hc (hdirs d hd) (-1) (Or.inr rfl)).mp hc'
      simp only [neg_one_mul] at hm
      have hc2 := mem_BZ.mp hc
      rw [List.all_eq_true] at h3
      have h4 := h3 (cls4 n c.1) (List.mem_range.mpr (by
        have := cls4_le n c.1 hc2.1 hc2.2.1; omega))
      rw [List.all_eq_true] at h4
      have h5 := h4 (cls4 n c.2) (List.mem_range.mpr (by
        have := cls4_le n c.2 hc2.2.2.1 hc2.2.2.2; omega))
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h5
      rcases h5 with h5 | h5
      · rw [hm] at h5; exact absurd h5 (by simp)
      · exact h5)
  have hle : ∑ c ∈ BZ n, (if c ∈ SZ S then Bf dirs (Gc n L) c else Af n D dirs (Gc n L) c) ≤
      ∑ c ∈ BZ n, Mty D dirs L (cls4 n c.1) (cls4 n c.2) := by
    apply Finset.sum_le_sum
    intro c hc
    rw [Af_ty hn D dirs hdirs L hc, Bf_ty hn dirs hdirs L hc, Mty]
    split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _
  have hsum : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      Mty D dirs L (cls4 n (i : ℤ)) (cls4 n (j : ℤ)) = D * target := by
    have : ∀ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Mty D dirs L (cls4 n (i : ℤ))
        (cls4 n (j : ℤ)) = ∑ w ∈ E8, Mty D dirs L (cls4 n (i : ℤ)) w +
          ((n : ℤ) - 8) * Mty D dirs L (cls4 n (i : ℤ)) 4 := fun i _ =>
      sum_cls4 hn (fun w => Mty D dirs L (cls4 n (i : ℤ)) w)
    rw [Finset.sum_congr rfl this, sum_cls4 hn (fun v => ∑ w ∈ E8, Mty D dirs L v w +
      ((n : ℤ) - 8) * Mty D dirs L v 4), ← htarget, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hsum2 : ∑ c ∈ BZ n, Mty D dirs L (cls4 n c.1) (cls4 n c.2) = D * target := by
    rw [sum_BZ]; exact hsum
  have : D * (tm dirs n S : ℤ) ≤ D * target := by linarith
  have := le_of_mul_le_mul_left this hD
  omega



/-! ### The table for queens -/

/-- Flow table for queens (in half units), by position classes. -/
private def LQ : List (ℕ × ℕ × ℤ × ℤ × ℕ) :=
  [(1, 1, -1, 1, 1), (1, 1, 0, 1, 4), (1, 1, 1, -1, 1), (1, 1, 1, 0, 4), (1, 1, 1, 1, 6), (1, 2, -1, 1, 1), (1, 2, 0, 1, 2), (1, 2, 1, -1, 3), (1, 2, 1, 0, 4), (1, 2, 1, 1, 6), (1, 3, -1, -1, 1), (1, 3, -1, 1, 1), (1, 3, 1, -1, 5), (1, 3, 1, 0, 4), (1, 3, 1, 1, 5), (1, 4, -1, -1, 1), (1, 4, 0, -1, 2), (1, 4, 1, -1, 6), (1, 4, 1, 0, 4), (1, 4, 1, 1, 3), (1, 5, -1, -1, 1), (1, 5, 0, -1, 4), (1, 5, 1, -1, 6), (1, 5, 1, 0, 4), (1, 5, 1, 1, 1), (2, 1, -1, 1, 3), (2, 1, 0, 1, 4), (2, 1, 1, -1, 1), (2, 1, 1, 0, 2), (2, 1, 1, 1, 6), (2, 2, -1, 1, 3), (2, 2, 0, 1, 2), (2, 2, 1, -1, 3), (2, 2, 1, 0, 2), (2, 2, 1, 1, 4), (2, 3, -1, -1, 2), (2, 3, -1, 1, 2), (2, 3, 1, -1, 4), (2, 3, 1, 0, 2), (2, 3, 1, 1, 4), (2, 4, -1, -1, 3), (2, 4, 0, -1, 2), (2, 4, 1, -1, 4), (2, 4, 1, 0, 2), (2, 4, 1, 1, 3), (2, 5, -1, -1, 3), (2, 5, 0, -1, 4), (2, 5, 1, -1, 6), (2, 5, 1, 0, 2), (2, 5, 1, 1, 1), (3, 1, -1, -1, 1), (3, 1, -1, 1, 5), (3, 1, 0, 1, 4), (3, 1, 1, -1, 1), (3, 1, 1, 1, 5), (3, 2, -1, -1, 2), (3, 2, -1, 1, 4), (3, 2, 0, 1, 2), (3, 2, 1, -1, 2), (3, 2, 1, 1, 4), (3, 3, -1, -1, 2), (3, 3, -1, 1, 2), (3, 3, 1, -1, 2), (3, 3, 1, 1, 2), (3, 4, -1, -1, 4), (3, 4, -1, 1, 2), (3, 4, 0, -1, 2), (3, 4, 1, -1, 4), (3, 4, 1, 1, 2), (3, 5, -1, -1, 5), (3, 5, -1, 1, 1), (3, 5, 0, -1, 4), (3, 5, 1, -1, 5), (3, 5, 1, 1, 1), (4, 1, -1, -1, 1), (4, 1, -1, 0, 2), (4, 1, -1, 1, 6), (4, 1, 0, 1, 4), (4, 1, 1, 1, 3), (4, 2, -1, -1, 3), (4, 2, -1, 0, 2), (4, 2, -1, 1, 4), (4, 2, 0, 1, 2), (4, 2, 1, 1, 3), (4, 3, -1, -1, 4), (4, 3, -1, 0, 2), (4, 3, -1, 1, 4), (4, 3, 1, -1, 2), (4, 3, 1, 1, 2), (4, 4, -1, -1, 4), (4, 4, -1, 0, 2), (4, 4, -1, 1, 3), (4, 4, 0, -1, 2), (4, 4, 1, -1, 3), (4, 5, -1, -1, 6), (4, 5, -1, 0, 2), (4, 5, -1, 1, 1), (4, 5, 0, -1, 4), (4, 5, 1, -1, 3), (5, 1, -1, -1, 1), (5, 1, -1, 0, 4), (5, 1, -1, 1, 6), (5, 1, 0, 1, 4), (5, 1, 1, 1, 1), (5, 2, -1, -1, 3), (5, 2, -1, 0, 4), (5, 2, -1, 1, 6), (5, 2, 0, 1, 2), (5, 2, 1, 1, 1), (5, 3, -1, -1, 5), (5, 3, -1, 0, 4), (5, 3, -1, 1, 5), (5, 3, 1, -1, 1), (5, 3, 1, 1, 1), (5, 4, -1, -1, 6), (5, 4, -1, 0, 4), (5, 4, -1, 1, 3), (5, 4, 0, -1, 2), (5, 4, 1, -1, 1), (5, 5, -1, -1, 6), (5, 5, -1, 0, 4), (5, 5, -1, 1, 1), (5, 5, 0, -1, 4), (5, 5, 1, -1, 1)]
/-- Queen directions are unit steps. -/
private lemma queenDirs_unit : ∀ d ∈ queenDirs, unitDir d := by
  simp [queenDirs, unitDir]

/-- Casting the targets `k (n - 2)²` to `ℤ`. -/
private lemma cast_target (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    ((k * (n - 2) ^ 2 : ℕ) : ℤ) = k * ((n : ℤ) - 8 + 6) ^ 2 := by
  push_cast [Nat.cast_sub hn]
  ring

/-- Queens, `n ≥ 8`. -/
private theorem queen_ge8 {n : ℕ} (hn : 8 ≤ n) {S : Finset (ℕ × ℕ)} (hS : S ⊆ board n) :
    tm queenDirs n S ≤ 8 * (n - 2) ^ 2 := by
  have c0 : ∑ v ∈ E8, ∑ w ∈ E8, Mty 2 queenDirs LQ v w = 576 := by decide +kernel
  have c1 : ∑ v ∈ E8, Mty 2 queenDirs LQ v 4 + ∑ w ∈ E8, Mty 2 queenDirs LQ 4 w = 192 := by
    decide +kernel
  have c2 : Mty 2 queenDirs LQ 4 4 = 16 := by decide +kernel
  refine general hn hS 2 (by norm_num) queenDirs queenDirs_unit LQ (by decide +kernel) _ ?_
  rw [c0, c1, c2, cast_target n (by omega)]
  ring

/-- Queens, `n = 7`, with the same table. -/
private theorem queen7 {S : Finset (ℕ × ℕ)} (hS : S ⊆ board 7) :
    tm queenDirs 7 S ≤ 200 :=
  leaf hS 2 (by norm_num) queenDirs (fun d c => tabC LQ (cls3 7 c.1) (cls3 7 c.2) d) [] [] 200
    (by decide +kernel) (by decide +kernel) (by simp) (by simp)


/-! ### The border placement -/

/-- Membership in the border placement. -/
private lemma mem_SZ_border {n : ℕ} {c : ℤ × ℤ} :
    c ∈ SZ (border n) ↔ c ∈ BZ n ∧ (c.1 = 0 ∨ c.1 = n - 1 ∨ c.2 = 0 ∨ c.2 = n - 1) := by
  constructor
  · intro h
    simp only [SZ, Finset.mem_map, border, Finset.mem_filter] at h
    obtain ⟨p, ⟨hp, hb⟩, rfl⟩ := h
    refine ⟨Finset.mem_map_of_mem emb hp, ?_⟩
    simp only [board, Finset.mem_product, Finset.mem_range] at hp
    simp only [emb_apply]
    omega
  · rintro ⟨h1, h2⟩
    have h1' := mem_BZ.mp h1
    rw [mem_SZ h1'.1 h1'.2.2.1]
    simp only [border, Finset.mem_filter, board, Finset.mem_product, Finset.mem_range]
    omega

/-- The interior squares. -/
private def intr (n : ℕ) (c : ℤ × ℤ) : Prop :=
  1 ≤ c.1 ∧ c.1 ≤ (n : ℤ) - 2 ∧ 1 ≤ c.2 ∧ c.2 ≤ (n : ℤ) - 2

/-- Interior squares are decidable. -/
private instance (n : ℕ) : DecidablePred (intr n) := fun c => by unfold intr; infer_instance

/-- For the border placement the empty squares are exactly the interior squares. -/
private lemma E_border {n : ℕ} {c : ℤ × ℤ} : E n (border n) c ↔ intr n c := by
  unfold E intr
  rw [mem_SZ_border, mem_BZ]
  omega

/-- For the border placement every interior square is reached from every direction. -/
private lemma Y_border {n : ℕ} {d c : ℤ × ℤ} (hd : unitDir d) (hd0 : d ≠ (0, 0)) :
    Y n (border n) d c = if intr n c then 1 else 0 := by
  split_ifs with hc
  · apply le_antisymm (Y_le_one _ _ _ _)
    obtain ⟨d1, d2, d3, d4⟩ := hd
    have hc' := hc
    obtain ⟨c1, c2, c3, c4⟩ := hc'
    have hex : ∃ m : ℕ, ¬ intr n (sh c d (-((m : ℤ) + 1))) := by
      refine ⟨n - 3, fun h => ?_⟩
      obtain ⟨e1, e2, e3, e4⟩ := h
      simp only [sh] at e1 e2 e3 e4
      push_cast [Nat.cast_sub (show 3 ≤ n by omega)] at e1 e2 e3 e4
      have : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
        by_contra hh; push Not at hh; exact hd0 (Prod.ext hh.1 hh.2)
      rcases this with h | h
      · rcases (show d.1 = 1 ∨ d.1 = -1 by omega) with h' | h' <;> rw [h'] at e1 e2 <;> linarith
      · rcases (show d.2 = 1 ∨ d.2 = -1 by omega) with h' | h' <;> rw [h'] at e3 e4 <;> linarith
    classical
    let k := Nat.find hex
    have hk : ¬ intr n (sh c d (-((k : ℤ) + 1))) := Nat.find_spec hex
    have hmin : ∀ j < k, intr n (sh c d (-((j : ℤ) + 1))) := fun j hj => by
      have := Nat.find_min hex hj; push Not at this; simpa using this
    have hkn : k ≤ n - 3 := Nat.find_min' hex (by
      intro h
      obtain ⟨e1, e2, e3, e4⟩ := h
      simp only [sh] at e1 e2 e3 e4
      push_cast [Nat.cast_sub (show 3 ≤ n by omega)] at e1 e2 e3 e4
      have : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
        by_contra hh; push Not at hh; exact hd0 (Prod.ext hh.1 hh.2)
      rcases this with h | h
      · rcases (show d.1 = 1 ∨ d.1 = -1 by omega) with h' | h' <;> rw [h'] at e1 e2 <;> linarith
      · rcases (show d.2 = 1 ∨ d.2 = -1 by omega) with h' | h' <;> rw [h'] at e3 e4 <;> linarith)
    -- all squares before the stop are interior
    have hall : ∀ j < k + 1, intr n (sh c d (-(j : ℤ))) := by
      intro j hj
      rcases j with _ | j
      · simpa [sh_zero] using hc
      · have := hmin j (by omega); push_cast; exact this
    have hprev : intr n (sh c d (-(k : ℤ))) := hall k (by omega)
    have hstop : sh c d (-((k : ℤ) + 1)) ∈ SZ (border n) := by
      rw [mem_SZ_border, mem_BZ]
      obtain ⟨f1, f2, f3, f4⟩ := hprev
      simp only [intr, sh, not_and_or, not_le] at hk f1 f2 f3 f4 ⊢
      constructor
      · constructor <;> [skip; constructor] <;> [skip; skip; constructor] <;> nlinarith
      · rcases hk with h | h | h | h
        · left; nlinarith
        · right; left; nlinarith
        · right; right; left; nlinarith
        · right; right; right; nlinarith
    unfold Y
    calc 1 = (if (sh c d (-((k : ℤ) + 1)) ∈ SZ (border n) ∧
          ∀ j < k + 1, E n (border n) (sh c d (-(j : ℤ)))) then 1 else 0) := by
            rw [if_pos ⟨hstop, fun j hj => E_border.mpr (hall j hj)⟩]
      _ ≤ _ := Finset.single_le_sum (f := fun k : ℕ => if (sh c d (-((k : ℤ) + 1)) ∈
          SZ (border n) ∧ ∀ j < k + 1, E n (border n) (sh c d (-(j : ℤ)))) then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  · exact Y_eq_zero_of_not_E (fun h => hc (E_border.mp h))

/-- There are `(n - 2)²` interior squares. -/
private lemma count_interior {n : ℕ} (hn : 2 ≤ n) :
    ∑ c ∈ BZ n, (if intr n c then 1 else 0 : ℕ) = (n - 2) ^ 2 := by
  rw [BZ, Finset.sum_map, board, Finset.sum_product]
  have h1 : ∀ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (if intr n (emb (i, j)) then 1 else 0 : ℕ) =
        if 1 ≤ i ∧ i ≤ n - 2 then n - 2 else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : ∀ j ∈ Finset.range n, (if intr n (emb (i, j)) then 1 else 0 : ℕ) =
        if (1 ≤ i ∧ i ≤ n - 2) ∧ (1 ≤ j ∧ j ≤ n - 2) then 1 else 0 := by
      intro j hj
      rw [Finset.mem_range] at hj
      apply if_congr _ rfl rfl
      simp only [intr, emb_apply]
      omega
    rw [Finset.sum_congr rfl this]
    split_ifs with h
    · simp only [h, true_and]
      rw [Finset.sum_boole]
      have : (Finset.range n).filter (fun j => 1 ≤ j ∧ j ≤ n - 2) = Finset.Icc 1 (n - 2) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
      rw [this, Nat.card_Icc]; simp
    · simp [h]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul]
  have : (Finset.range n).filter (fun i => 1 ≤ i ∧ i ≤ n - 2) = Finset.Icc 1 (n - 2) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc, Nat.add_sub_cancel, sq]

/-- Exchanging a sum over the pieces with a sum over the list of directions. -/
private lemma sum_swap_list (S : Finset (ℕ × ℕ)) (L : List (ℤ × ℤ)) (f : ℕ × ℕ → ℤ × ℤ → ℕ) :
    ∑ p ∈ S, (L.map (f p)).sum = (L.map fun d => ∑ p ∈ S, f p d).sum := by
  induction L with
  | nil => simp
  | cons d L ih => simp [Finset.sum_add_distrib, ih]

/-- The border placement has `#dirs · (n - 2)²` moves. -/
private lemma total_border {n : ℕ} (hn : 2 ≤ n) (dirs : List (ℤ × ℤ))
    (hdirs : ∀ d ∈ dirs, unitDir d ∧ d ≠ (0, 0)) :
    tm dirs n (border n) = dirs.length * (n - 2) ^ 2 := by
  unfold tm
  rw [sum_swap_list]
  have : ∀ d ∈ dirs, ∑ p ∈ border n, rayMoves n (border n) p d = (n - 2) ^ 2 := by
    intro d hd
    rw [sum_ray_eq, ← count_interior hn]
    apply Finset.sum_congr rfl
    intro c _
    exact Y_border (hdirs d hd).1 (hdirs d hd).2
  rw [List.map_congr_left this]
  simp

/-- The border placement lies on the board. -/
private lemma border_sub (n : ℕ) : border n ⊆ board n := Finset.filter_subset _ _


/-! ### The `6 × 6` board -/

/-- Flow certificate 0 for the `6 × 6` board (leaf `In = [(0, 1), (1, 5), (4, 5)]`, `Out = []`). -/
private def q6_t0 : List (ℤ × ℤ × ℤ × ℤ × ℕ) :=
  [(1, 1, 1, 1, 9), (1, 1, 1, 3, 6), (1, 1, 1, 4, 3), (1, 1, 2, 1, 7), (1, 1, 2, 2, 6), (1, 1,
    2, 4, 3), (1, 1, 3, 1, 5), (1, 1, 3, 2, 4), (1, 1, 3, 3, 3), (1, 1, 4, 1, 2), (1, 1, 4, 2,
    2), (1, 1, 4, 3, 1), (1, -1, 1, 1, 3), (1, -1, 1, 2, 6), (1, -1, 1, 3, 6), (1, -1, 1, 4,
    9), (1, -1, 2, 1, 3), (1, -1, 2, 2, 3), (1, -1, 2, 3, 6), (1, -1, 3, 2, 3), (1, -1, 3, 3,
    1), (1, -1, 3, 4, 6), (1, -1, 4, 3, 3), (1, -1, 4, 4, 3), (-1, 1, 1, 1, 3), (-1, 1, 1, 2,
    3), (-1, 1, 1, 3, 2), (-1, 1, 2, 1, 6), (-1, 1, 2, 2, 5), (-1, 1, 2, 3, 2), (-1, 1, 2, 4,
    2), (-1, 1, 3, 1, 8), (-1, 1, 3, 2, 5), (-1, 1, 3, 3, 5), (-1, 1, 3, 4, 3), (-1, 1, 4, 1,
    8), (-1, 1, 4, 2, 8), (-1, 1, 4, 3, 6), (-1, 1, 4, 4, 3), (-1, -1, 1, 3, 2), (-1, -1, 1,
    4, 3), (-1, -1, 2, 1, 1), (-1, -1, 2, 2, 3), (-1, -1, 2, 4, 5), (-1, -1, 3, 1, 2), (-1,
    -1, 3, 2, 4), (-1, -1, 3, 3, 6), (-1, -1, 4, 0, 1), (-1, -1, 4, 1, 3), (-1, -1, 4, 2, 5),
    (-1, -1, 4, 3, 7), (-1, -1, 4, 4, 9), (1, 0, 1, 2, 6), (1, 0, 1, 3, 6), (1, 0, 1, 4, 9),
    (1, 0, 2, 2, 3), (1, 0, 2, 3, 3), (1, 0, 2, 4, 6), (1, 0, 3, 4, 3), (-1, 0, 2, 3, 1), (-1,
    0, 2, 4, 2), (-1, 0, 3, 1, 2), (-1, 0, 3, 2, 3), (-1, 0, 3, 3, 4), (-1, 0, 3, 4, 5), (-1,
    0, 4, 1, 5), (-1, 0, 4, 2, 6), (-1, 0, 4, 3, 7), (-1, 0, 4, 4, 8), (0, 1, 1, 1, 8), (0, 1,
    1, 2, 5), (0, 1, 1, 3, 2), (0, 1, 2, 1, 7), (0, 1, 2, 2, 4), (0, 1, 2, 3, 1), (0, 1, 3, 1,
    7), (0, 1, 3, 2, 4), (0, 1, 3, 3, 1), (0, 1, 4, 1, 6), (0, 1, 4, 2, 3), (0, 1, 5, 1, 1),
    (0, -1, 2, 3, 3), (0, -1, 2, 4, 6), (0, -1, 3, 2, 1), (0, -1, 3, 3, 4), (0, -1, 3, 4, 7)]

/-- Flow certificate 1 for the `6 × 6` board (leaf `In = [(0, 1), (1, 5)]`, `Out = [(4, 5)]`). -/
private def q6_t1 : List (ℤ × ℤ × ℤ × ℤ × ℕ) :=
  [(1, 1, 1, 1, 6), (1, 1, 1, 3, 4), (1, 1, 1, 4, 2), (1, 1, 2, 1, 4), (1, 1, 2, 2, 4), (1, 1,
    2, 4, 2), (1, 1, 3, 1, 3), (1, 1, 3, 2, 2), (1, 1, 3, 3, 2), (1, 1, 4, 1, 2), (1, 1, 4, 2,
    1), (1, 1, 4, 5, 2), (1, -1, 1, 1, 2), (1, -1, 1, 2, 4), (1, -1, 1, 3, 4), (1, -1, 1, 4,
    6), (1, -1, 2, 1, 2), (1, -1, 2, 2, 2), (1, -1, 2, 3, 4), (1, -1, 3, 2, 2), (1, -1, 3, 4,
    2), (1, -1, 4, 4, 2), (1, -1, 5, 4, 2), (-1, 1, 1, 1, 2), (-1, 1, 1, 2, 2), (-1, 1, 2, 1,
    4), (-1, 1, 2, 2, 2), (-1, 1, 2, 3, 1), (-1, 1, 3, 1, 4), (-1, 1, 3, 2, 3), (-1, 1, 3, 3,
    2), (-1, 1, 3, 4, 2), (-1, 1, 4, 1, 5), (-1, 1, 4, 2, 4), (-1, 1, 4, 3, 4), (-1, 1, 4, 4,
    2), (-1, 1, 4, 5, 2), (-1, -1, 1, 2, 2), (-1, -1, 1, 3, 2), (-1, -1, 1, 4, 2), (-1, -1, 2,
    3, 4), (-1, -1, 2, 4, 4), (-1, -1, 3, 1, 2), (-1, -1, 3, 2, 2), (-1, -1, 3, 3, 2), (-1,
    -1, 3, 4, 6), (-1, -1, 4, 0, 2), (-1, -1, 4, 1, 2), (-1, -1, 4, 2, 4), (-1, -1, 4, 3, 4),
    (-1, -1, 4, 4, 4), (1, 0, 1, 2, 4), (1, 0, 1, 3, 4), (1, 0, 1, 4, 6), (1, 0, 2, 2, 2), (1,
    0, 2, 3, 2), (1, 0, 2, 4, 4), (1, 0, 3, 4, 2), (-1, 0, 3, 1, 2), (-1, 0, 3, 2, 2), (-1, 0,
    3, 3, 2), (-1, 0, 4, 0, 1), (-1, 0, 4, 1, 4), (-1, 0, 4, 2, 4), (-1, 0, 4, 3, 4), (-1, 0,
    4, 4, 2), (-1, 0, 4, 5, 2), (0, 1, 1, 1, 6), (0, 1, 1, 2, 4), (0, 1, 1, 3, 2), (0, 1, 2,
    1, 5), (0, 1, 2, 2, 3), (0, 1, 2, 3, 1), (0, 1, 3, 1, 4), (0, 1, 3, 2, 2), (0, 1, 4, 1,
    3), (0, 1, 4, 2, 1), (0, 1, 4, 5, 2), (0, -1, 2, 2, 2), (0, -1, 2, 3, 4), (0, -1, 2, 4,
    6), (0, -1, 3, 3, 2), (0, -1, 3, 4, 4), (0, -1, 4, 2, 2), (0, -1, 4, 3, 4), (0, -1, 4, 4,
    6)]

/-- Flow certificate 2 for the `6 × 6` board (leaf `In = [(0, 1), (5, 4)]`, `Out = [(1, 5)]`). -/
private def q6_t2 : List (ℤ × ℤ × ℤ × ℤ × ℕ) :=
  [(1, 1, 1, 1, 6), (1, 1, 1, 3, 3), (1, 1, 1, 4, 2), (1, 1, 1, 5, 2), (1, 1, 2, 1, 6), (1, 1,
    2, 2, 4), (1, 1, 2, 4, 1), (1, 1, 3, 1, 4), (1, 1, 3, 2, 4), (1, 1, 3, 3, 2), (1, 1, 4, 1,
    2), (1, 1, 4, 2, 2), (1, 1, 4, 3, 2), (1, 1, 5, 1, 2), (1, -1, 1, 1, 2), (1, -1, 1, 2, 4),
    (1, -1, 1, 3, 3), (1, -1, 1, 4, 4), (1, -1, 2, 1, 2), (1, -1, 2, 2, 1), (1, -1, 2, 3, 2),
    (1, -1, 2, 4, 6), (1, -1, 3, 3, 4), (1, -1, 3, 4, 4), (1, -1, 4, 2, 2), (1, -1, 4, 3, 2),
    (1, -1, 4, 4, 2), (-1, 1, 1, 1, 2), (-1, 1, 1, 2, 2), (-1, 1, 1, 5, 2), (-1, 1, 2, 1, 4),
    (-1, 1, 2, 2, 2), (-1, 1, 2, 3, 2), (-1, 1, 3, 1, 4), (-1, 1, 3, 2, 4), (-1, 1, 3, 4, 2),
    (-1, 1, 4, 1, 6), (-1, 1, 4, 2, 2), (-1, 1, 4, 3, 4), (-1, 1, 4, 4, 2), (-1, -1, 0, 4, 2),
    (-1, -1, 2, 2, 2), (-1, -1, 2, 3, 2), (-1, -1, 2, 4, 2), (-1, -1, 3, 1, 2), (-1, -1, 3, 3,
    4), (-1, -1, 3, 4, 4), (-1, -1, 4, 0, 2), (-1, -1, 4, 1, 2), (-1, -1, 4, 2, 4), (-1, -1,
    4, 4, 6), (1, 0, 1, 2, 5), (1, 0, 1, 3, 4), (1, 0, 1, 4, 3), (1, 0, 1, 5, 2), (1, 0, 2, 2,
    3), (1, 0, 2, 3, 2), (1, 0, 2, 4, 1), (1, 0, 3, 2, 1), (-1, 0, 3, 1, 2), (-1, 0, 3, 2, 2),
    (-1, 0, 3, 3, 2), (-1, 0, 4, 1, 4), (-1, 0, 4, 2, 4), (-1, 0, 4, 3, 4), (0, 1, 1, 1, 4),
    (0, 1, 1, 2, 2), (0, 1, 1, 5, 2), (0, 1, 2, 1, 4), (0, 1, 2, 2, 2), (0, 1, 3, 1, 4), (0,
    1, 3, 2, 2), (0, 1, 4, 1, 2), (0, -1, 1, 1, 1), (0, -1, 1, 2, 3), (0, -1, 1, 3, 5), (0,
    -1, 1, 4, 7), (0, -1, 2, 2, 2), (0, -1, 2, 3, 4), (0, -1, 2, 4, 6), (0, -1, 3, 2, 2), (0,
    -1, 3, 3, 4), (0, -1, 3, 4, 6), (0, -1, 4, 2, 2), (0, -1, 4, 3, 4), (0, -1, 4, 4, 6)]

/-- Flow certificate 3 for the `6 × 6` board (leaf `In = [(0, 1)]`, `Out = [(1, 5), (5, 4)]`). -/
private def q6_t3 : List (ℤ × ℤ × ℤ × ℤ × ℕ) :=
  [(1, 1, 1, 1, 6), (1, 1, 1, 3, 2), (1, 1, 1, 4, 2), (1, 1, 1, 5, 2), (1, 1, 2, 1, 4), (1, 1,
    2, 2, 4), (1, 1, 3, 1, 4), (1, 1, 3, 2, 2), (1, 1, 3, 3, 2), (1, 1, 4, 1, 2), (1, 1, 4, 2,
    2), (1, 1, 5, 4, 2), (1, -1, 1, 1, 2), (1, -1, 1, 2, 4), (1, -1, 1, 3, 4), (1, -1, 1, 4,
    4), (1, -1, 2, 1, 2), (1, -1, 2, 2, 2), (1, -1, 2, 3, 2), (1, -1, 2, 4, 5), (1, -1, 3, 3,
    3), (1, -1, 3, 4, 2), (1, -1, 4, 2, 1), (1, -1, 4, 4, 2), (1, -1, 5, 4, 2), (-1, 1, 1, 1,
    2), (-1, 1, 1, 2, 1), (-1, 1, 1, 5, 2), (-1, 1, 2, 1, 3), (-1, 1, 2, 2, 2), (-1, 1, 3, 1,
    4), (-1, 1, 3, 2, 2), (-1, 1, 3, 3, 2), (-1, 1, 3, 4, 2), (-1, 1, 4, 1, 4), (-1, 1, 4, 2,
    4), (-1, 1, 4, 3, 4), (-1, 1, 4, 4, 2), (-1, 1, 4, 5, 2), (-1, -1, 0, 4, 2), (-1, -1, 1,
    0, 1), (-1, -1, 1, 3, 1), (-1, -1, 1, 4, 2), (-1, -1, 2, 1, 3), (-1, -1, 2, 3, 2), (-1,
    -1, 2, 4, 3), (-1, -1, 3, 1, 1), (-1, -1, 3, 2, 5), (-1, -1, 3, 3, 2), (-1, -1, 3, 4, 4),
    (-1, -1, 4, 0, 1), (-1, -1, 4, 1, 2), (-1, -1, 4, 2, 3), (-1, -1, 4, 3, 7), (-1, -1, 4, 4,
    4), (1, 0, 1, 2, 6), (1, 0, 1, 3, 4), (1, 0, 1, 4, 2), (1, 0, 1, 5, 2), (1, 0, 2, 2, 4),
    (1, 0, 2, 3, 2), (1, 0, 3, 2, 2), (1, 0, 5, 4, 2), (-1, 0, 1, 5, 2), (-1, 0, 2, 3, 1),
    (-1, 0, 2, 4, 2), (-1, 0, 3, 1, 2), (-1, 0, 3, 2, 2), (-1, 0, 3, 3, 3), (-1, 0, 3, 4, 4),
    (-1, 0, 4, 0, 1), (-1, 0, 4, 1, 4), (-1, 0, 4, 2, 4), (-1, 0, 4, 3, 5), (-1, 0, 4, 4, 6),
    (0, 1, 1, 1, 5), (0, 1, 1, 2, 3), (0, 1, 1, 3, 1), (0, 1, 1, 5, 2), (0, 1, 2, 1, 4), (0,
    1, 2, 2, 2), (0, 1, 3, 1, 5), (0, 1, 3, 2, 3), (0, 1, 3, 3, 1), (0, 1, 4, 1, 4), (0, 1, 4,
    2, 2), (0, 1, 5, 1, 1), (0, 1, 5, 4, 2), (0, -1, 1, 2, 2), (0, -1, 1, 3, 4), (0, -1, 1, 4,
    6), (0, -1, 2, 2, 2), (0, -1, 2, 3, 4), (0, -1, 2, 4, 6), (0, -1, 3, 3, 2), (0, -1, 3, 4,
    4), (0, -1, 4, 4, 2), (0, -1, 5, 4, 2)]

/-- Flow certificate 4 for the `6 × 6` board (leaf `In = [(1, 5), (4, 0)]`, `Out = [(0, 1)]`). -/
private def q6_t4 : List (ℤ × ℤ × ℤ × ℤ × ℕ) :=
  [(1, 1, 1, 1, 4), (1, 1, 1, 2, 6), (1, 1, 1, 3, 4), (1, 1, 1, 4, 2), (1, 1, 2, 1, 3), (1, 1,
    2, 2, 2), (1, 1, 2, 3, 4), (1, 1, 2, 4, 2), (1, 1, 3, 1, 4), (1, 1, 3, 2, 1), (1, 1, 3, 4,
    2), (1, 1, 4, 1, 2), (1, 1, 4, 2, 2), (1, -1, 1, 0, 2), (1, -1, 1, 2, 2), (1, -1, 1, 3,
    4), (1, -1, 1, 4, 6), (1, -1, 2, 2, 2), (1, -1, 2, 3, 4), (1, -1, 3, 2, 2), (1, -1, 3, 4,
    4), (1, -1, 4, 3, 2), (1, -1, 4, 4, 2), (1, -1, 5, 4, 2), (-1, 1, 0, 1, 2), (-1, 1, 1, 1,
    2), (-1, 1, 1, 2, 1), (-1, 1, 2, 1, 3), (-1, 1, 2, 3, 2), (-1, 1, 2, 4, 2), (-1, 1, 3, 2,
    4), (-1, 1, 3, 3, 4), (-1, 1, 3, 4, 2), (-1, 1, 4, 1, 6), (-1, 1, 4, 2, 6), (-1, 1, 4, 3,
    4), (-1, 1, 4, 4, 2), (-1, 1, 4, 5, 2), (-1, -1, 0, 1, 2), (-1, -1, 1, 3, 2), (-1, -1, 1,
    4, 2), (-1, -1, 2, 2, 2), (-1, -1, 2, 4, 4), (-1, -1, 3, 1, 2), (-1, -1, 3, 2, 2), (-1,
    -1, 3, 3, 4), (-1, -1, 3, 4, 2), (-1, -1, 4, 1, 2), (-1, -1, 4, 2, 4), (-1, -1, 4, 3, 4),
    (-1, -1, 4, 4, 6), (1, 0, 1, 1, 7), (1, 0, 1, 2, 6), (1, 0, 1, 3, 6), (1, 0, 1, 4, 6), (1,
    0, 2, 1, 5), (1, 0, 2, 2, 4), (1, 0, 2, 3, 4), (1, 0, 2, 4, 4), (1, 0, 3, 1, 3), (1, 0, 3,
    2, 2), (1, 0, 3, 3, 2), (1, 0, 3, 4, 2), (1, 0, 4, 1, 1), (-1, 0, 0, 1, 2), (-1, 0, 3, 1,
    2), (-1, 0, 3, 2, 2), (-1, 0, 3, 3, 2), (-1, 0, 4, 1, 4), (-1, 0, 4, 2, 4), (-1, 0, 4, 3,
    4), (-1, 0, 4, 4, 2), (0, 1, 0, 1, 2), (0, 1, 1, 1, 3), (0, 1, 1, 2, 1), (0, 1, 2, 1, 4),
    (0, 1, 2, 2, 2), (0, 1, 3, 1, 5), (0, 1, 3, 2, 3), (0, 1, 3, 3, 1), (0, -1, 2, 3, 2), (0,
    -1, 2, 4, 4), (0, -1, 3, 3, 2), (0, -1, 3, 4, 4), (0, -1, 4, 3, 2), (0, -1, 4, 4, 4)]

/-- Flow certificate 5 for the `6 × 6` board (leaf `In = [(4, 0)]`, `Out = [(0, 1), (1, 5)]`). -/
private def q6_t5 : List (ℤ × ℤ × ℤ × ℤ × ℕ) :=
  [(1, 1, 1, 1, 4), (1, 1, 1, 2, 6), (1, 1, 1, 3, 2), (1, 1, 1, 4, 2), (1, 1, 1, 5, 2), (1, 1,
    2, 1, 4), (1, 1, 2, 2, 2), (1, 1, 2, 3, 4), (1, 1, 3, 1, 4), (1, 1, 3, 2, 2), (1, 1, 3, 4,
    2), (1, 1, 4, 1, 2), (1, 1, 4, 2, 2), (1, -1, 1, 0, 2), (1, -1, 1, 1, 2), (1, -1, 1, 2,
    3), (1, -1, 1, 3, 3), (1, -1, 1, 4, 4), (1, -1, 2, 1, 1), (1, -1, 2, 2, 1), (1, -1, 2, 3,
    2), (1, -1, 2, 4, 6), (1, -1, 3, 3, 4), (1, -1, 3, 4, 3), (1, -1, 4, 2, 2), (1, -1, 4, 3,
    1), (1, -1, 4, 4, 2), (1, -1, 5, 4, 1), (-1, 1, 0, 1, 2), (-1, 1, 1, 1, 2), (-1, 1, 1, 5,
    2), (-1, 1, 2, 1, 2), (-1, 1, 2, 3, 1), (-1, 1, 3, 2, 3), (-1, 1, 3, 3, 2), (-1, 1, 3, 4,
    1), (-1, 1, 4, 1, 5), (-1, 1, 4, 2, 4), (-1, 1, 4, 3, 3), (-1, 1, 4, 4, 2), (-1, -1, 0, 1,
    2), (-1, -1, 0, 4, 2), (-1, -1, 1, 3, 2), (-1, -1, 1, 4, 2), (-1, -1, 2, 2, 2), (-1, -1,
    2, 3, 2), (-1, -1, 2, 4, 4), (-1, -1, 3, 1, 1), (-1, -1, 3, 2, 2), (-1, -1, 3, 3, 2), (-1,
    -1, 3, 4, 4), (-1, -1, 4, 1, 2), (-1, -1, 4, 2, 3), (-1, -1, 4, 3, 4), (-1, -1, 4, 4, 4),
    (1, 0, 1, 1, 6), (1, 0, 1, 2, 6), (1, 0, 1, 3, 5), (1, 0, 1, 4, 3), (1, 0, 1, 5, 2), (1,
    0, 2, 1, 4), (1, 0, 2, 2, 4), (1, 0, 2, 3, 3), (1, 0, 2, 4, 1), (1, 0, 3, 1, 2), (1, 0, 3,
    2, 2), (1, 0, 3, 3, 1), (-1, 0, 0, 1, 2), (-1, 0, 2, 1, 1), (-1, 0, 2, 2, 1), (-1, 0, 2,
    3, 1), (-1, 0, 3, 1, 3), (-1, 0, 3, 2, 3), (-1, 0, 3, 3, 3), (-1, 0, 3, 4, 2), (-1, 0, 4,
    1, 5), (-1, 0, 4, 2, 5), (-1, 0, 4, 3, 5), (-1, 0, 4, 4, 4), (-1, 0, 4, 5, 1), (0, 1, 0,
    1, 2), (0, 1, 1, 1, 2), (0, 1, 1, 5, 2), (0, 1, 2, 1, 4), (0, 1, 2, 2, 2), (0, 1, 3, 1,
    6), (0, 1, 3, 2, 4), (0, 1, 3, 3, 2), (0, 1, 5, 1, 1), (0, -1, 1, 2, 1), (0, -1, 1, 3, 3),
    (0, -1, 1, 4, 5), (0, -1, 2, 2, 2), (0, -1, 2, 3, 3), (0, -1, 2, 4, 5), (0, -1, 3, 3, 2),
    (0, -1, 3, 4, 4), (0, -1, 4, 3, 2), (0, -1, 4, 4, 4), (0, -1, 5, 4, 1)]

/-- Flow certificate 6 for the `6 × 6` board (leaf `In = [(5, 4)]`, `Out = [(0, 1), (4, 0)]`). -/
private def q6_t6 : List (ℤ × ℤ × ℤ × ℤ × ℕ) :=
  [(1, 1, 1, 1, 4), (1, 1, 1, 2, 6), (1, 1, 1, 3, 3), (1, 1, 1, 4, 2), (1, 1, 2, 1, 4), (1, 1,
    2, 2, 2), (1, 1, 2, 3, 4), (1, 1, 2, 4, 1), (1, 1, 3, 1, 3), (1, 1, 3, 2, 2), (1, 1, 3, 4,
    2), (1, 1, 4, 1, 2), (1, 1, 4, 2, 1), (1, 1, 5, 1, 2), (1, -1, 1, 0, 2), (1, -1, 1, 1, 2),
    (1, -1, 1, 2, 4), (1, -1, 1, 3, 3), (1, -1, 1, 4, 3), (1, -1, 2, 1, 2), (1, -1, 2, 2, 1),
    (1, -1, 2, 3, 1), (1, -1, 2, 4, 4), (1, -1, 3, 3, 2), (1, -1, 3, 4, 3), (1, -1, 4, 0, 2),
    (1, -1, 4, 3, 1), (1, -1, 4, 4, 2), (-1, 1, 0, 1, 2), (-1, 1, 1, 1, 2), (-1, 1, 1, 3, 2),
    (-1, 1, 2, 1, 2), (-1, 1, 2, 2, 4), (-1, 1, 3, 1, 6), (-1, 1, 3, 2, 2), (-1, 1, 3, 3, 2),
    (-1, 1, 3, 4, 2), (-1, 1, 4, 1, 4), (-1, 1, 4, 2, 4), (-1, 1, 4, 3, 4), (-1, 1, 4, 4, 2),
    (-1, -1, 0, 1, 2), (-1, -1, 0, 4, 1), (-1, -1, 1, 2, 1), (-1, -1, 1, 3, 2), (-1, -1, 1, 4,
    2), (-1, -1, 2, 2, 2), (-1, -1, 2, 3, 3), (-1, -1, 2, 4, 4), (-1, -1, 3, 3, 4), (-1, -1,
    3, 4, 5), (-1, -1, 4, 0, 2), (-1, -1, 4, 1, 2), (-1, -1, 4, 2, 2), (-1, -1, 4, 4, 6), (1,
    0, 1, 1, 5), (1, 0, 1, 2, 5), (1, 0, 1, 3, 4), (1, 0, 1, 4, 4), (1, 0, 1, 5, 1), (1, 0, 2,
    1, 3), (1, 0, 2, 2, 3), (1, 0, 2, 3, 2), (1, 0, 2, 4, 2), (1, 0, 3, 1, 1), (1, 0, 3, 2,
    2), (1, 0, 4, 0, 2), (-1, 0, 0, 1, 2), (-1, 0, 2, 3, 2), (-1, 0, 3, 2, 2), (-1, 0, 3, 3,
    4), (-1, 0, 4, 0, 2), (-1, 0, 4, 1, 2), (-1, 0, 4, 2, 4), (-1, 0, 4, 3, 6), (0, 1, 0, 1,
    2), (0, 1, 1, 1, 2), (0, 1, 2, 1, 5), (0, 1, 2, 2, 3), (0, 1, 2, 3, 1), (0, 1, 3, 1, 6),
    (0, 1, 3, 2, 4), (0, 1, 3, 3, 2), (0, 1, 4, 1, 6), (0, 1, 4, 2, 4), (0, 1, 4, 3, 2), (0,
    -1, 0, 4, 2), (0, -1, 1, 3, 2), (0, -1, 1, 4, 4), (0, -1, 2, 2, 1), (0, -1, 2, 3, 3), (0,
    -1, 2, 4, 5), (0, -1, 3, 3, 2), (0, -1, 3, 4, 4), (0, -1, 4, 0, 2), (0, -1, 4, 2, 1), (0,
    -1, 4, 3, 3), (0, -1, 4, 4, 5)]

/-- Flow certificate 7 for the `6 × 6` board (leaf `In = []`, `Out = [(0, 1), (4, 0), (5, 4)]`). -/
private def q6_t7 : List (ℤ × ℤ × ℤ × ℤ × ℕ) :=
  [(1, 1, 1, 1, 4), (1, 1, 1, 2, 6), (1, 1, 1, 3, 3), (1, 1, 1, 4, 2), (1, 1, 2, 1, 3), (1, 1,
    2, 2, 2), (1, 1, 2, 3, 4), (1, 1, 2, 4, 1), (1, 1, 3, 1, 4), (1, 1, 3, 2, 1), (1, 1, 3, 4,
    2), (1, 1, 4, 1, 2), (1, 1, 4, 2, 2), (1, 1, 5, 1, 2), (1, 1, 5, 4, 2), (1, -1, 1, 0, 2),
    (1, -1, 1, 1, 2), (1, -1, 1, 2, 3), (1, -1, 1, 3, 4), (1, -1, 1, 4, 4), (1, -1, 2, 1, 1),
    (1, -1, 2, 2, 2), (1, -1, 2, 3, 2), (1, -1, 2, 4, 4), (1, -1, 3, 2, 1), (1, -1, 3, 3, 2),
    (1, -1, 3, 4, 2), (1, -1, 4, 0, 2), (1, -1, 4, 4, 2), (1, -1, 5, 4, 2), (-1, 1, 0, 1, 2),
    (-1, 1, 1, 1, 2), (-1, 1, 1, 2, 1), (-1, 1, 1, 3, 2), (-1, 1, 2, 1, 3), (-1, 1, 2, 2, 4),
    (-1, 1, 3, 1, 6), (-1, 1, 3, 2, 2), (-1, 1, 3, 3, 2), (-1, 1, 4, 1, 4), (-1, 1, 4, 2, 4),
    (-1, 1, 4, 3, 2), (-1, 1, 4, 4, 2), (-1, 1, 4, 5, 2), (-1, -1, 0, 1, 2), (-1, -1, 0, 4,
    1), (-1, -1, 1, 4, 2), (-1, -1, 2, 1, 2), (-1, -1, 2, 3, 1), (-1, -1, 2, 4, 2), (-1, -1,
    3, 0, 1), (-1, -1, 3, 2, 4), (-1, -1, 3, 3, 2), (-1, -1, 3, 4, 3), (-1, -1, 4, 0, 2), (-1,
    -1, 4, 1, 3), (-1, -1, 4, 2, 2), (-1, -1, 4, 3, 6), (-1, -1, 4, 4, 4), (1, 0, 1, 1, 5),
    (1, 0, 1, 2, 5), (1, 0, 1, 3, 5), (1, 0, 1, 4, 4), (1, 0, 1, 5, 1), (1, 0, 2, 1, 3), (1,
    0, 2, 2, 3), (1, 0, 2, 3, 3), (1, 0, 2, 4, 2), (1, 0, 3, 1, 1), (1, 0, 3, 2, 1), (1, 0, 3,
    3, 1), (1, 0, 5, 4, 2), (-1, 0, 0, 1, 2), (-1, 0, 2, 2, 1), (-1, 0, 2, 3, 2), (-1, 0, 2,
    4, 1), (-1, 0, 3, 2, 3), (-1, 0, 3, 3, 4), (-1, 0, 3, 4, 3), (-1, 0, 4, 0, 2), (-1, 0, 4,
    1, 2), (-1, 0, 4, 2, 5), (-1, 0, 4, 3, 6), (-1, 0, 4, 4, 5), (0, 1, 0, 1, 2), (0, 1, 1, 1,
    3), (0, 1, 1, 2, 1), (0, 1, 2, 1, 4), (0, 1, 2, 2, 2), (0, 1, 3, 1, 4), (0, 1, 3, 2, 2),
    (0, 1, 3, 3, 1), (0, 1, 4, 1, 5), (0, 1, 4, 2, 3), (0, 1, 4, 3, 1), (0, -1, 0, 4, 1), (0,
    -1, 1, 3, 2), (0, -1, 1, 4, 4), (0, -1, 2, 2, 2), (0, -1, 2, 3, 4), (0, -1, 2, 4, 6), (0,
    -1, 3, 2, 2), (0, -1, 3, 3, 4), (0, -1, 3, 4, 6), (0, -1, 4, 0, 2), (0, -1, 4, 3, 1), (0,
    -1, 4, 4, 3), (0, -1, 5, 4, 2)]

/-- Leaf 0 of the branch and bound tree for the `6 × 6` board. -/
private lemma q6_leaf0 {S : Finset (ℕ × ℕ)} (hS : S ⊆ board 6)
    (hi0 : ((0, 1) : ℕ × ℕ) ∈ S)
    (hi1 : ((1, 5) : ℕ × ℕ) ∈ S)
    (hi2 : ((4, 5) : ℕ × ℕ) ∈ S) :
    tm queenDirs 6 S ≤ 128 :=
  leaf hS 3 (by norm_num) queenDirs (tab q6_t0) [(0, 1), (1, 5), (4, 5)] [] 128
    (by decide +kernel) (by decide +kernel) (by simp [hi0, hi1, hi2]) (by simp)

/-- Leaf 1 of the branch and bound tree for the `6 × 6` board. -/
private lemma q6_leaf1 {S : Finset (ℕ × ℕ)} (hS : S ⊆ board 6)
    (hi0 : ((0, 1) : ℕ × ℕ) ∈ S)
    (hi1 : ((1, 5) : ℕ × ℕ) ∈ S)
    (ho0 : ((4, 5) : ℕ × ℕ) ∉ S) :
    tm queenDirs 6 S ≤ 128 :=
  leaf hS 2 (by norm_num) queenDirs (tab q6_t1) [(0, 1), (1, 5)] [(4, 5)] 128
    (by decide +kernel) (by decide +kernel) (by simp [hi0, hi1]) (by simp [ho0])

/-- Leaf 2 of the branch and bound tree for the `6 × 6` board. -/
private lemma q6_leaf2 {S : Finset (ℕ × ℕ)} (hS : S ⊆ board 6)
    (hi0 : ((0, 1) : ℕ × ℕ) ∈ S)
    (hi1 : ((5, 4) : ℕ × ℕ) ∈ S)
    (ho0 : ((1, 5) : ℕ × ℕ) ∉ S) :
    tm queenDirs 6 S ≤ 128 :=
  leaf hS 2 (by norm_num) queenDirs (tab q6_t2) [(0, 1), (5, 4)] [(1, 5)] 128
    (by decide +kernel) (by decide +kernel) (by simp [hi0, hi1]) (by simp [ho0])

/-- Leaf 3 of the branch and bound tree for the `6 × 6` board. -/
private lemma q6_leaf3 {S : Finset (ℕ × ℕ)} (hS : S ⊆ board 6)
    (hi0 : ((0, 1) : ℕ × ℕ) ∈ S)
    (ho0 : ((1, 5) : ℕ × ℕ) ∉ S)
    (ho1 : ((5, 4) : ℕ × ℕ) ∉ S) :
    tm queenDirs 6 S ≤ 128 :=
  leaf hS 2 (by norm_num) queenDirs (tab q6_t3) [(0, 1)] [(1, 5), (5, 4)] 128
    (by decide +kernel) (by decide +kernel) (by simp [hi0]) (by simp [ho0, ho1])

/-- Leaf 4 of the branch and bound tree for the `6 × 6` board. -/
private lemma q6_leaf4 {S : Finset (ℕ × ℕ)} (hS : S ⊆ board 6)
    (hi0 : ((1, 5) : ℕ × ℕ) ∈ S)
    (hi1 : ((4, 0) : ℕ × ℕ) ∈ S)
    (ho0 : ((0, 1) : ℕ × ℕ) ∉ S) :
    tm queenDirs 6 S ≤ 128 :=
  leaf hS 2 (by norm_num) queenDirs (tab q6_t4) [(1, 5), (4, 0)] [(0, 1)] 128
    (by decide +kernel) (by decide +kernel) (by simp [hi0, hi1]) (by simp [ho0])

/-- Leaf 5 of the branch and bound tree for the `6 × 6` board. -/
private lemma q6_leaf5 {S : Finset (ℕ × ℕ)} (hS : S ⊆ board 6)
    (hi0 : ((4, 0) : ℕ × ℕ) ∈ S)
    (ho0 : ((0, 1) : ℕ × ℕ) ∉ S)
    (ho1 : ((1, 5) : ℕ × ℕ) ∉ S) :
    tm queenDirs 6 S ≤ 128 :=
  leaf hS 2 (by norm_num) queenDirs (tab q6_t5) [(4, 0)] [(0, 1), (1, 5)] 128
    (by decide +kernel) (by decide +kernel) (by simp [hi0]) (by simp [ho0, ho1])

/-- Leaf 6 of the branch and bound tree for the `6 × 6` board. -/
private lemma q6_leaf6 {S : Finset (ℕ × ℕ)} (hS : S ⊆ board 6)
    (hi0 : ((5, 4) : ℕ × ℕ) ∈ S)
    (ho0 : ((0, 1) : ℕ × ℕ) ∉ S)
    (ho1 : ((4, 0) : ℕ × ℕ) ∉ S) :
    tm queenDirs 6 S ≤ 128 :=
  leaf hS 2 (by norm_num) queenDirs (tab q6_t6) [(5, 4)] [(0, 1), (4, 0)] 128
    (by decide +kernel) (by decide +kernel) (by simp [hi0]) (by simp [ho0, ho1])

/-- Leaf 7 of the branch and bound tree for the `6 × 6` board. -/
private lemma q6_leaf7 {S : Finset (ℕ × ℕ)} (hS : S ⊆ board 6)
    (ho0 : ((0, 1) : ℕ × ℕ) ∉ S)
    (ho1 : ((4, 0) : ℕ × ℕ) ∉ S)
    (ho2 : ((5, 4) : ℕ × ℕ) ∉ S) :
    tm queenDirs 6 S ≤ 128 :=
  leaf hS 2 (by norm_num) queenDirs (tab q6_t7) [] [(0, 1), (4, 0), (5, 4)] 128
    (by decide +kernel) (by decide +kernel) (by simp) (by simp [ho0, ho1, ho2])

/-- Upper bound for queens on the `6 × 6` board: branch and bound on the squares `(0, 1)`,
`(1, 5)`, `(4, 5)`, `(5, 4)`, `(4, 0)`, with a flow certificate at each of the eight leaves. -/
private theorem queen6_le {S : Finset (ℕ × ℕ)} (hS : S ⊆ board 6) :
    tm queenDirs 6 S ≤ 128 := by
  by_cases h0 : ((0, 1) : ℕ × ℕ) ∈ S
  · by_cases h1 : ((1, 5) : ℕ × ℕ) ∈ S
    · by_cases h2 : ((4, 5) : ℕ × ℕ) ∈ S
      · exact q6_leaf0 hS h0 h1 h2
      · exact q6_leaf1 hS h0 h1 h2
    · by_cases h2 : ((5, 4) : ℕ × ℕ) ∈ S
      · exact q6_leaf2 hS h0 h2 h1
      · exact q6_leaf3 hS h0 h1 h2
  · by_cases h1 : ((4, 0) : ℕ × ℕ) ∈ S
    · by_cases h2 : ((1, 5) : ℕ × ℕ) ∈ S
      · exact q6_leaf4 hS h2 h1 h0
      · exact q6_leaf5 hS h1 h0 h2
    · by_cases h2 : ((5, 4) : ℕ × ℕ) ∈ S
      · exact q6_leaf6 hS h2 h0 h1
      · exact q6_leaf7 hS h0 h1 h2

/-! ### Conclusion -/

/-- Upper bounds for `a`. -/
private lemma a_le {n X : ℕ} (h : ∀ S ⊆ board n, tm queenDirs n S ≤ X) : a n ≤ X :=
  Finset.sup_le fun S hS => (totalMoves_eq n S).trans_le (h S (Finset.mem_powerset.mp hS))

/-- Lower bound for `a` from the border placement. -/
private lemma a_border {n : ℕ} (hn : 2 ≤ n) : 8 * (n - 2) ^ 2 ≤ a n := by
  have h := Finset.le_sup (f := totalMoves n) (Finset.mem_powerset.mpr (border_sub n))
  rw [totalMoves_eq, total_border hn queenDirs (by simp [queenDirs, unitDir])] at h
  exact h

/-- Jones's conjecture holds: `a(n) = 8 (n - 2)²` for every `n ≥ 6`. -/
theorem result : statement := by
  intro n hn
  obtain rfl | rfl | h8 : n = 6 ∨ n = 7 ∨ 8 ≤ n := by omega
  · exact le_antisymm ((a_le fun S hS => queen6_le hS).trans_eq (by norm_num))
      (a_border (by norm_num))
  · exact le_antisymm ((a_le fun S hS => queen7 hS).trans_eq (by norm_num))
      (a_border (by norm_num))
  · exact le_antisymm (a_le fun S hS => queen_ge8 h8 hS) (a_border (by omega))

end Math0.Frontier.A275815

#math0_settles Math0.Frontier.A275815.result Math0.Statements.A275815.statement
