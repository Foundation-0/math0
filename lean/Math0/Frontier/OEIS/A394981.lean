/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A394981
import Math0.Audit

/-!
# Bar tilings of the smallest-perimeter rectangle: `a(n + 1) = 4 a(n)` for odd `n ≥ 3` (A394981)

We prove the conjecture of A394981 in the form of `statement`: for every odd `n = 2m + 1 ≥ 3`,
`a(2m + 2) = 4 a(2m + 1)`. Write `R(n)` for the number of tilings of the rectangle of `n` by the
bars `1 × 1, …, 1 × n` (each used once); the rectangles are `S = (m + 1) × (2m + 1)` for
`n = 2m + 1` and `B = (m + 1) × (2m + 3)` for `n = 2m + 2`.

*The definition, made explicit.* `search` enumerates exactly the tilings (`search_eq`: it sums
over all assignments of placements to the tiles that partition the free cells, read through the
bitmask encoding), and the labelling it builds has the length of the covering tile in the field
of every cell (`field_cell`). Since the bars have pairwise different lengths, a symmetry fixing a
tiling fixes every tile; looking at the tiles in the corners, no non-identity symmetry of a
non-square rectangle with at least two rows and columns can do so (`stabCount_eq_one`). Hence
`a(n) = R(n) / 4` for `n ≥ 3` (`a_odd`, `a_even`).

*Structure.* In `S` the bar `2m + 1` is a full row, so the bars `m + 1, …, 2m + 1` are horizontal;
each crosses the middle column `m`, and since two of them do not fit in one row, every row holds
exactly one of them. So the middle column is covered by the long bars and the short bars
`1, …, m` avoid it. In `B` the bars `m + 2, …, 2m + 2` are horizontal, cross column `m + 1` and
again one lies in each row. The bar `m + 1` of `B` is then either vertical, and then a full first
or last column (bar `2m + 2` must fit beside it), or horizontal, and then it shares its row with
bar `m + 2`, the two filling that row in one of two orders.

*Four bijections.* If bar `m + 1` is the first (last) column of `B`, deleting it and the column
`m + 2` (`m + 1`) of `B`, and shortening every long bar by one, gives a tiling of `S`
(`PhiV`/`PsiV`). If bar `m + 1` is horizontal, replacing the row of `m + 1` and `m + 2` by the
bar `2m + 1`, deleting the columns `m + 1`, `m + 2` and shortening the other long bars by two,
gives a tiling of `S` (`PhiH`/`PsiH`). Hence `R(2m + 2) = 4 R(2m + 1)` (`card_big`).

*Divisibility.* The reflections of `S` act freely on its tilings, distinguished by the row of
bar `2m + 1` (with the row of bar `2m` to break the tie at the middle row) and by the column
(`0` or `1`) of bar `2m`; so `4 ∣ R(2m + 1)` (`four_dvd_small`), and
`a(2m + 2) = R(2m + 2) / 4 = R(2m + 1) = 4 (R(2m + 1) / 4) = 4 a(2m + 1)`.
-/

namespace Math0.Frontier.A394981
open Math0.Statements.A394981 Finset

/-! ## Bits -/

/-- Bit `p` of `∑_{i ∈ s} 2 ^ i` is set iff `p ∈ s`. -/
private theorem testBit_sum_two_pow (s : Finset ℕ) (p : ℕ) :
    (∑ i ∈ s, 2 ^ i).testBit p = true ↔ p ∈ s := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

/-- The set of set bits of `X`. -/
private def bset (X : ℕ) : Finset ℕ := X.bitIndices.toFinset

/-- Membership in `bset X` is the bit test. -/
private theorem mem_bset {X p : ℕ} : p ∈ bset X ↔ X.testBit p = true := by
  simp [bset]

/-- `X` is the sum of `2 ^ i` over its set bits. -/
private theorem sum_bset (X : ℕ) : ∑ i ∈ bset X, 2 ^ i = X :=
  Finset.sum_toFinset_bitIndices_two_pow X

/-- The set bits of `∑_{i ∈ s} 2 ^ i` are `s`. -/
private theorem bset_sum (s : Finset ℕ) : bset (∑ i ∈ s, 2 ^ i) = s :=
  Finset.toFinset_bitIndices_sum_two_pow s

/-- Clearing the lowest set bit. -/
private theorem land_sub_one (v Y : ℕ) :
    Nat.land (2 ^ (v + 1) * Y + 2 ^ v) (2 ^ (v + 1) * Y + 2 ^ v - 1) = 2 ^ (v + 1) * Y := by
  have h1 : 2 ^ v < 2 ^ (v + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ v - 1 < 2 ^ (v + 1) := by omega
  have hv : 1 ≤ 2 ^ v := Nat.one_le_two_pow
  have e : 2 ^ (v + 1) * Y + 2 ^ v - 1 = 2 ^ (v + 1) * Y + (2 ^ v - 1) := by omega
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro j
  have h0 : (0:ℕ) < 2 ^ (v + 1) := by positivity
  rw [Nat.land_eq, Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1,
    Nat.testBit_two_pow_mul_add _ h2]
  conv_rhs => rw [← Nat.add_zero (2 ^ (v + 1) * Y), Nat.testBit_two_pow_mul_add _ h0]
  split_ifs with hj
  · rcases Nat.lt_or_ge j v with h | h
    · simp [show v ≠ j by omega]
    · simp [Nat.testBit_two_pow_sub_one, show ¬ j < v by omega]
  · simp

/-- `sumBits g fuel X` is `∑ g (2 ^ i)` over the set bits `i` of `X` when `fuel` is at least
their number. -/
private theorem sumBits_eq (g : ℕ → ℕ) : ∀ (fuel X : ℕ), (bset X).card ≤ fuel →
    sumBits g fuel X = ∑ i ∈ bset X, g (2 ^ i)
  | 0, X, h => by
      have : bset X = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [this, Finset.sum_empty]; rfl
  | fuel + 1, X, h => by
      show (bif Nat.beq X 0 then 0 else
        g (X - Nat.land X (X - 1)) + sumBits g fuel (Nat.land X (X - 1))) = _
      by_cases hX : X = 0
      · subst hX
        have : bset 0 = ∅ := by simp [bset]
        rw [this, Finset.sum_empty]; rfl
      · have hb : Nat.beq X 0 = false := by
          cases h : Nat.beq X 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) hX
        rw [hb, cond_false]
        have hne : (bset X).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h0
          apply hX
          rw [← sum_bset X, h0, Finset.sum_empty]
        set s := bset X with hs
        set v := s.min' hne with hv
        have hvs : v ∈ s := Finset.min'_mem s hne
        set Z := ∑ i ∈ s.erase v, 2 ^ i with hZ
        have hdvd : 2 ^ (v + 1) ∣ Z := by
          apply Finset.dvd_sum
          intro i hi
          have h1 : v ≤ i := Finset.min'_le s i (Finset.mem_of_mem_erase hi)
          have h2 : i ≠ v := Finset.ne_of_mem_erase hi
          exact Nat.pow_dvd_pow 2 (by omega)
        obtain ⟨Y, hY⟩ := hdvd
        have hX' : X = 2 ^ (v + 1) * Y + 2 ^ v := by
          rw [← hY, hZ]
          conv_lhs => rw [← sum_bset X]
          rw [← hs, ← Finset.add_sum_erase s _ hvs]
          ring
        have hland : Nat.land X (X - 1) = Z := by
          rw [hY, hX']; exact land_sub_one v Y
        have hsub : X - Nat.land X (X - 1) = 2 ^ v := by
          rw [hland, hY, hX', Nat.add_sub_cancel_left]
        have hcard : (bset Z).card ≤ fuel := by
          rw [hZ, bset_sum, Finset.card_erase_of_mem hvs]
          omega
        rw [hsub, hland, sumBits_eq g fuel Z hcard, hZ, bset_sum]
        exact Finset.add_sum_erase s (fun i => g (2 ^ i)) hvs

/-! ## Placements and tilings -/

/-- A placement `(i, j, d)`: first cell in row `i`, column `j`; vertical iff `d`. -/
private abbrev Pl := ℕ × ℕ × Bool

/-- The default placement, used outside the range of tiles. -/
private def dflt : Pl := (0, 0, false)

/-- Cell `(a, b)` lies in the bar of length `k` placed at `p`. -/
private def inBar (p : Pl) (k a b : ℕ) : Prop :=
  if p.2.2 = true then b = p.2.1 ∧ p.1 ≤ a ∧ a < p.1 + k else a = p.1 ∧ p.2.1 ≤ b ∧ b < p.2.1 + k

/-- Membership in a bar is decidable. -/
private instance (p : Pl) (k a b : ℕ) : Decidable (inBar p k a b) := by
  unfold inBar; infer_instance

/-- The bar of length `k` at `p` fits in the `r × c` rectangle (and is horizontal if `k = 1`). -/
private def Fits (r c : ℕ) (p : Pl) (k : ℕ) : Prop :=
  if p.2.2 = true then p.1 + k ≤ r ∧ p.2.1 < c ∧ 2 ≤ k else p.1 < r ∧ p.2.1 + k ≤ c

/-- The cells of the bar of length `k` at `p`. -/
private def cellsOf (p : Pl) (k : ℕ) : Finset (ℕ × ℕ) :=
  (range k).image (fun t => if p.2.2 = true then (p.1 + t, p.2.1) else (p.1, p.2.1 + t))

/-- A cell lies in `cellsOf p k` iff it lies in the bar. -/
private theorem mem_cellsOf {p : Pl} {k a b : ℕ} : (a, b) ∈ cellsOf p k ↔ inBar p k a b := by
  obtain ⟨i, j, d⟩ := p
  cases d
  · simp only [cellsOf, inBar, mem_image, mem_range, Bool.false_eq_true, if_false, Prod.mk.injEq]
    constructor
    · rintro ⟨t, ht, h1, h2⟩; omega
    · rintro ⟨h1, h2, h3⟩; exact ⟨b - j, by omega, by omega, by omega⟩
  · simp only [cellsOf, inBar, mem_image, mem_range, if_true, Prod.mk.injEq]
    constructor
    · rintro ⟨t, ht, h1, h2⟩; omega
    · rintro ⟨h1, h2, h3⟩; exact ⟨a - i, by omega, by omega, by omega⟩

/-- The cells of the `r × c` rectangle. -/
private def rectS (r c : ℕ) : Finset (ℕ × ℕ) := range r ×ˢ range c

/-- Membership in the rectangle. -/
private theorem mem_rectS {r c a b : ℕ} : (a, b) ∈ rectS r c ↔ a < r ∧ b < c := by
  simp [rectS]

/-- A bar that fits only covers cells of the rectangle. -/
private theorem inBar_lt {r c : ℕ} {p : Pl} {k a b : ℕ} (hf : Fits r c p k) (h : inBar p k a b) :
    a < r ∧ b < c := by
  obtain ⟨i, j, d⟩ := p
  cases d <;> simp only [Fits, inBar, Bool.false_eq_true, if_false, if_true] at hf h <;> omega

/-- `P` places the tiles `1, …, k` (tile `k'` at `P k'`) so that they partition `S`. -/
private def ValidOn (r c k : ℕ) (P : ℕ → Pl) (S : Finset (ℕ × ℕ)) : Prop :=
  (∀ k', 1 ≤ k' → k' ≤ k → Fits r c (P k') k') ∧
  (∀ k' a b, 1 ≤ k' → k' ≤ k → inBar (P k') k' a b → (a, b) ∈ S) ∧
  (∀ a b, (a, b) ∈ S → ∃ k', 1 ≤ k' ∧ k' ≤ k ∧ inBar (P k') k' a b) ∧
  (∀ a b k1 k2, 1 ≤ k1 → k1 ≤ k → 1 ≤ k2 → k2 ≤ k →
    inBar (P k1) k1 a b → inBar (P k2) k2 a b → k1 = k2)

/-- A tiling of the `r × c` rectangle by the bars `1 × 1, …, 1 × n`. -/
private def Valid (r c n : ℕ) (P : ℕ → Pl) : Prop := ValidOn r c n P (rectS r c)

/-- Peeling off the largest tile: `P` places the tiles `1, …, k + 1` as a partition of `S` iff
tile `k + 1` fits inside `S` and the other tiles partition the rest. -/
private theorem validOn_succ {r c k : ℕ} {P : ℕ → Pl} {S : Finset (ℕ × ℕ)} :
    ValidOn r c (k + 1) P S ↔ Fits r c (P (k + 1)) (k + 1) ∧ cellsOf (P (k + 1)) (k + 1) ⊆ S ∧
      ValidOn r c k P (S \ cellsOf (P (k + 1)) (k + 1)) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1 _ (by omega) le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, b⟩ := x
      exact h2 _ a b (by omega) le_rfl (mem_cellsOf.mp hx)
    · intro k' hk1 hk2; exact h1 k' hk1 (by omega)
    · intro k' a b hk1 hk2 hin
      rw [mem_sdiff, mem_cellsOf]
      refine ⟨h2 k' a b hk1 (by omega) hin, fun h => ?_⟩
      have := h4 a b k' (k + 1) hk1 (by omega) (by omega) le_rfl hin h
      omega
    · intro a b hab
      rw [mem_sdiff, mem_cellsOf] at hab
      obtain ⟨k', hk1, hk2, hin⟩ := h3 a b hab.1
      refine ⟨k', hk1, ?_, hin⟩
      rcases Nat.lt_or_ge k' (k + 1) with h | h
      · omega
      · have : k' = k + 1 := by omega
        subst this; exact absurd hin hab.2
    · intro a b k1 k2 h1' h2' h3' h4'
      exact h4 a b k1 k2 h1' (by omega) h3' (by omega)
  · rintro ⟨hf, hsub, h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k' hk1 hk2
      rcases Nat.lt_or_ge k' (k + 1) with h | h
      · exact h1 k' hk1 (by omega)
      · have : k' = k + 1 := by omega
        subst this; exact hf
    · intro k' a b hk1 hk2 hin
      rcases Nat.lt_or_ge k' (k + 1) with h | h
      · exact (mem_sdiff.mp (h2 k' a b hk1 (by omega) hin)).1
      · have : k' = k + 1 := by omega
        subst this; exact hsub (mem_cellsOf.mpr hin)
    · intro a b hab
      by_cases hc : (a, b) ∈ cellsOf (P (k + 1)) (k + 1)
      · exact ⟨k + 1, by omega, le_rfl, mem_cellsOf.mp hc⟩
      · obtain ⟨k', hk1, hk2, hin⟩ := h3 a b (mem_sdiff.mpr ⟨hab, hc⟩)
        exact ⟨k', hk1, by omega, hin⟩
    · intro a b k1 k2 hk1 hk1' hk2 hk2' hin1 hin2
      have key : ∀ k', 1 ≤ k' → k' ≤ k → inBar (P k') k' a b →
          ¬ inBar (P (k + 1)) (k + 1) a b := by
        intro k' h h' hin hin'
        exact (mem_sdiff.mp (h2 k' a b h h' hin)).2 (mem_cellsOf.mpr hin')
      rcases Nat.lt_or_ge k1 (k + 1) with h | h <;> rcases Nat.lt_or_ge k2 (k + 1) with h' | h'
      · exact h4 a b k1 k2 hk1 (by omega) hk2 (by omega) hin1 hin2
      · have : k2 = k + 1 := by omega
        subst this; exact absurd hin2 (key k1 hk1 (by omega) hin1)
      · have : k1 = k + 1 := by omega
        subst this; exact absurd hin1 (key k2 hk2 (by omega) hin2)
      · omega

/-- `ValidOn` only depends on the placements of the tiles `1, …, k`. -/
private theorem validOn_congr_imp {r c k : ℕ} {P Q : ℕ → Pl} {S : Finset (ℕ × ℕ)}
    (h : ∀ k', 1 ≤ k' → k' ≤ k → P k' = Q k') (hP : ValidOn r c k P S) : ValidOn r c k Q S := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨fun k' a b => ?_, fun k' a b c1 c2 hin => ?_, fun a b hab => ?_,
    fun a b k1 k2 a1 a2 a3 a4 a5 a6 => ?_⟩
  · rw [← h k' a b]; exact h1 k' a b
  · rw [← h k' c1 c2] at hin; exact h2 k' a b c1 c2 hin
  · obtain ⟨k', e1, e2, e3⟩ := h3 a b hab
    exact ⟨k', e1, e2, by rw [← h k' e1 e2]; exact e3⟩
  · rw [← h k1 a1 a2] at a5; rw [← h k2 a3 a4] at a6
    exact h4 a b k1 k2 a1 a2 a3 a4 a5 a6

/-- `ValidOn` only depends on the placements of the tiles `1, …, k` (iff form). -/
private theorem validOn_congr {r c k : ℕ} {P Q : ℕ → Pl} {S : Finset (ℕ × ℕ)}
    (h : ∀ k', 1 ≤ k' → k' ≤ k → P k' = Q k') : ValidOn r c k P S ↔ ValidOn r c k Q S :=
  ⟨validOn_congr_imp h, validOn_congr_imp fun k' h1 h2 => (h k' h1 h2).symm⟩

/-! ## The encoding used by `search` -/

/-- The index of the first cell of a placement. -/
private def idx (w : ℕ) (p : Pl) : ℕ := p.1 * w + p.2.1

/-- The index step along a placement. -/
private def step (w : ℕ) (p : Pl) : ℕ := if p.2.2 = true then w else 1

/-- The labelling built by `search` along the placements `P 1, …, P k`. -/
private def enc (w L : ℕ) (P : ℕ → Pl) : ℕ → ℕ
  | 0 => 0
  | k + 1 => enc w L P k + (k + 1) * barAt (2 ^ idx w (P (k + 1))) L (step w (P (k + 1))) (k + 1)

/-- `enc` only depends on the placements of the tiles `1, …, k`. -/
private theorem enc_congr {w L : ℕ} {P Q : ℕ → Pl} : ∀ k, (∀ k', 1 ≤ k' → k' ≤ k → P k' = Q k') →
    enc w L P k = enc w L Q k
  | 0, _ => rfl
  | k + 1, h => by
      simp only [enc]
      rw [enc_congr k (fun k' h1 h2 => h k' h1 (by omega)), h (k + 1) (by omega) le_rfl]

/-- The candidate placements inside the `r × c` rectangle. -/
private def Xs (r c : ℕ) : Finset Pl := range r ×ˢ (range c ×ˢ univ)

open Classical in
/-- All assignments of candidate placements to the tiles `1, …, k` (default elsewhere). -/
private noncomputable def Univ (r c : ℕ) : ℕ → Finset (ℕ → Pl)
  | 0 => {fun _ => dflt}
  | k + 1 => ((Univ r c k) ×ˢ Xs r c).image (fun x => Function.update x.1 (k + 1) x.2)

/-- `Univ r c k` consists of the assignments that are default outside `1, …, k` and use
candidate placements on `1, …, k`. -/
private theorem mem_Univ {r c : ℕ} : ∀ {k : ℕ} {P : ℕ → Pl}, P ∈ Univ r c k ↔
    (∀ k', (k' = 0 ∨ k < k') → P k' = dflt) ∧ (∀ k', 1 ≤ k' → k' ≤ k → P k' ∈ Xs r c)
  | 0, P => by
      classical
      simp only [Univ, mem_singleton]
      constructor
      · rintro rfl; exact ⟨fun _ _ => rfl, fun k' h1 h2 => by omega⟩
      · rintro ⟨h1, -⟩; funext k'; exact h1 k' (by omega)
  | k + 1, P => by
      classical
      simp only [Univ, mem_image, mem_product]
      constructor
      · rintro ⟨⟨Q, p⟩, ⟨hQ, hp⟩, rfl⟩
        rw [mem_Univ] at hQ
        refine ⟨fun k' hk' => ?_, fun k' h1 h2 => ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact hQ.1 k' (by omega)
        · by_cases e : k' = k + 1
          · subst e; simpa using hp
          · rw [Function.update_of_ne e]; exact hQ.2 k' h1 (by omega)
      · rintro ⟨h1, h2⟩
        refine ⟨⟨Function.update P (k + 1) dflt, P (k + 1)⟩, ⟨?_, h2 _ (by omega) le_rfl⟩, ?_⟩
        · rw [mem_Univ]
          dsimp only
          refine ⟨fun k' hk' => ?_, fun k' h1' h2' => ?_⟩
          · by_cases e : k' = k + 1
            · subst e; simp
            · rw [Function.update_of_ne e]; exact h1 k' (by omega)
          · rw [Function.update_of_ne (by omega)]; exact h2 k' h1' (by omega)
        · funext k'
          by_cases e : k' = k + 1
          · subst e; simp
          · simp [Function.update_of_ne e]

/-- Summing over `Univ r c (k + 1)` is summing over `Univ r c k` and the placement of tile
`k + 1`. -/
private theorem sum_Univ_succ {r c k : ℕ} (F : (ℕ → Pl) → ℕ) :
    ∑ P ∈ Univ r c (k + 1), F P =
      ∑ P ∈ Univ r c k, ∑ p ∈ Xs r c, F (Function.update P (k + 1) p) := by
  classical
  rw [Univ, sum_image, sum_product]
  rintro ⟨P, p⟩ hP ⟨Q, q⟩ hQ he
  simp only [coe_product, Set.mem_prod, mem_coe] at hP hQ
  have e1 : p = q := by have := congrFun he (k + 1); simpa using this
  have hP0 := (mem_Univ.mp hP.1).1 (k + 1) (by omega)
  have hQ0 := (mem_Univ.mp hQ.1).1 (k + 1) (by omega)
  have e2 : P = Q := by
    funext k'
    by_cases e : k' = k + 1
    · subst e; rw [hP0, hQ0]
    · have := congrFun he k'; simpa [Function.update_of_ne e] using this
  simp [e1, e2]

/-! ## Bitmasks of cell sets -/

/-- The bitmask of a set of cells, rows of length `w`. -/
private def bmC (w : ℕ) (S : Finset (ℕ × ℕ)) : ℕ := ∑ x ∈ S, 2 ^ (x.1 * w + x.2)

/-- Cell indices `a * w + b` with `b < w` determine the cell. -/
private theorem idx_inj {w a b a' b' : ℕ} (hb : b < w) (hb' : b' < w)
    (h : a * w + b = a' * w + b') : a = a' ∧ b = b' := by
  have hw : 0 < w := by omega
  have e1 : (a * w + b) / w = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hb, zero_add]
  have e2 : (a' * w + b') / w = a' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hb', zero_add]
  have e3 : a = a' := by rw [← e1, ← e2, h]
  subst e3
  exact ⟨rfl, by omega⟩

/-- The set bits of the bitmask of a cell set are the indices of its cells. -/
private theorem testBit_bmC {w : ℕ} {S : Finset (ℕ × ℕ)} (hS : ∀ x ∈ S, x.2 < w) (p : ℕ) :
    (bmC w S).testBit p = true ↔ ∃ x ∈ S, x.1 * w + x.2 = p := by
  have : bmC w S = ∑ y ∈ S.image (fun x => x.1 * w + x.2), 2 ^ y := by
    rw [sum_image]
    · rfl
    · intro x hx y hy hxy
      obtain ⟨e1, e2⟩ := idx_inj (hS x hx) (hS y hy) hxy
      exact Prod.ext e1 e2
  rw [this, testBit_sum_two_pow, mem_image]

/-- The bitmask of a set difference is the difference of the bitmasks. -/
private theorem bmC_sdiff {w : ℕ} {S B : Finset (ℕ × ℕ)} (h : B ⊆ S) :
    bmC w S - bmC w B = bmC w (S \ B) := by
  have := sum_sdiff (f := fun x : ℕ × ℕ => 2 ^ (x.1 * w + x.2)) h
  unfold bmC; omega

/-- A bitmask vanishes iff the cell set is empty. -/
private theorem bmC_eq_zero {w : ℕ} {S : Finset (ℕ × ℕ)} : bmC w S = 0 ↔ S = ∅ := by
  simp [bmC, Finset.sum_eq_zero_iff, Finset.eq_empty_iff_forall_notMem]

/-- `barAt` at the first cell of a placement, with the placement's step, is the sum over its
cells (in fields of `L` bits). -/
private theorem barAt_cells {w L : ℕ} (hw : 1 ≤ w) (hL : 1 ≤ L) (p : Pl) (k : ℕ) :
    barAt (2 ^ idx w p) L (step w p) k = ∑ x ∈ cellsOf p k, 2 ^ (L * (x.1 * w + x.2)) := by
  have hs : 1 ≤ L * step w p := by
    unfold step; split_ifs <;> nlinarith
  rw [barAt_eq hs, cellsOf, sum_image]
  · apply sum_congr rfl
    intro t _
    obtain ⟨i, j, d⟩ := p
    cases d <;> simp only [idx, step, Bool.false_eq_true, if_false, if_true] <;> congr 2 <;> ring
  · intro t1 _ t2 _ h
    obtain ⟨i, j, d⟩ := p
    cases d <;> simp at h <;> omega

/-- Cells of the rectangle have column `< w` when `c < w`. -/
private theorem rect_snd_lt {r c w : ℕ} (hcw : c < w) {S : Finset (ℕ × ℕ)} (hS : S ⊆ rectS r c) :
    ∀ x ∈ S, x.2 < w := by
  intro x hx
  have := hS hx
  obtain ⟨a, b⟩ := x
  rw [mem_rectS] at this
  simp only; omega

/-- The horizontal starts of tile `k + 1` inside `S`: bit `q` of `starts` is set iff the `k + 1`
cells from `q` along its row lie in `S` (and do not run past the last column). -/
private theorem starts_h {r c w : ℕ} (hcw : c < w) {S : Finset (ℕ × ℕ)} (hS : S ⊆ rectS r c)
    (k q : ℕ) : (starts (bmC w S) 1 (k + 1)).testBit q = true ↔
      q % w + k < c ∧ ∀ t ≤ k, (q / w, q % w + t) ∈ S := by
  have hS' := rect_snd_lt hcw hS
  have hq := Nat.div_add_mod' q w
  have hw : q % w < w := Nat.mod_lt _ (by omega)
  rw [testBit_starts]
  simp only [mul_one, testBit_bmC hS']
  constructor
  · intro h
    obtain ⟨x, hx, hxe⟩ := h 0 (by omega)
    have hx2 := hS' x hx
    have hxr := hS hx
    obtain ⟨x1, x2⟩ := x
    rw [mem_rectS] at hxr
    simp only at hxe hx2
    obtain ⟨-, e2⟩ := idx_inj hx2 hw (hxe.trans (by omega : q + 0 = q / w * w + q % w))
    have hlt : q % w + k < c := by
      by_contra hcon
      obtain ⟨y, hy, hye⟩ := h (c - q % w) (by omega)
      have hy2 := hS' y hy
      have hyr := hS hy
      obtain ⟨y1, y2⟩ := y
      rw [mem_rectS] at hyr
      simp only at hye hy2
      obtain ⟨-, e3⟩ := idx_inj hy2 hcw (hye.trans (by omega : q + (c - q % w) = q / w * w + c))
      omega
    refine ⟨hlt, fun t ht => ?_⟩
    obtain ⟨z, hz, hze⟩ := h t (by omega)
    have hz2 := hS' z hz
    obtain ⟨z1, z2⟩ := z
    simp only at hze hz2
    obtain ⟨e4, e5⟩ := idx_inj hz2 (by omega : q % w + t < w)
      (hze.trans (by omega : q + t = q / w * w + (q % w + t)))
    rw [e4, e5] at hz; exact hz
  · rintro ⟨h1, h2⟩ t ht
    exact ⟨(q / w, q % w + t), h2 t (by omega), by simp only; omega⟩

/-- The vertical starts of tile `k + 1` inside `S`: bit `q` of `starts` is set iff the `k + 1`
cells from `q` down its column lie in `S`. -/
private theorem starts_v {r c w : ℕ} (hcw : c < w) {S : Finset (ℕ × ℕ)} (hS : S ⊆ rectS r c)
    (k q : ℕ) : (starts (bmC w S) w (k + 1)).testBit q = true ↔
      q % w < c ∧ ∀ t ≤ k, (q / w + t, q % w) ∈ S := by
  have hS' := rect_snd_lt hcw hS
  have hq := Nat.div_add_mod' q w
  have hw : q % w < w := Nat.mod_lt _ (by omega)
  have key : ∀ t, q + t * w = (q / w + t) * w + q % w := by
    intro t; rw [add_mul]; omega
  rw [testBit_starts]
  simp only [testBit_bmC hS']
  constructor
  · intro h
    obtain ⟨x, hx, hxe⟩ := h 0 (by omega)
    have hxr := hS hx
    obtain ⟨x1, x2⟩ := x
    rw [mem_rectS] at hxr
    simp only at hxe
    obtain ⟨-, e2⟩ := idx_inj (by omega) hw (hxe.trans (by rw [key 0]))
    refine ⟨by omega, fun t ht => ?_⟩
    obtain ⟨z, hz, hze⟩ := h t (by omega)
    have hz2 := hS' z hz
    obtain ⟨z1, z2⟩ := z
    simp only at hze hz2
    obtain ⟨e4, e5⟩ := idx_inj hz2 hw (hze.trans (key t))
    rw [e4, e5] at hz; exact hz
  · rintro ⟨h1, h2⟩ t ht
    exact ⟨(q / w + t, q % w), h2 t (by omega), by simp only; rw [key t]⟩

/-- A horizontal bar lies in `S` iff each of its cells does. -/
private theorem cellsOf_sub_h {S : Finset (ℕ × ℕ)} (i j k : ℕ) :
    cellsOf (i, j, false) (k + 1) ⊆ S ↔ ∀ t ≤ k, (i, j + t) ∈ S := by
  simp only [cellsOf, Bool.false_eq_true, if_false, image_subset_iff, mem_range]
  exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩

/-- A vertical bar lies in `S` iff each of its cells does. -/
private theorem cellsOf_sub_v {S : Finset (ℕ × ℕ)} (i j k : ℕ) :
    cellsOf (i, j, true) (k + 1) ⊆ S ↔ ∀ t ≤ k, (i + t, j) ∈ S := by
  simp only [cellsOf, if_true, image_subset_iff, mem_range]
  exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩

/-- Summing over the set bits of `starts` is summing over the placements of tile `k + 1` with
the given orientation inside `S`. -/
private theorem sumBits_starts {r c w : ℕ} (hcw : c < w) {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ rectS r c) (k : ℕ) (d : Bool) (g : ℕ → ℕ) :
    sumBits g (r * w) (starts (bmC w S) (if d = true then w else 1) (k + 1)) =
      ∑ p ∈ (Xs r c).filter (fun p => p.2.2 = d ∧ cellsOf p (k + 1) ⊆ S), g (2 ^ idx w p) := by
  have hw0 : 0 < w := by omega
  -- membership in the set bits
  have hmem : ∀ q, q ∈ bset (starts (bmC w S) (if d = true then w else 1) (k + 1)) ↔
      (q / w, q % w, d) ∈ (Xs r c).filter (fun p => p.2.2 = d ∧ cellsOf p (k + 1) ⊆ S) := by
    intro q
    rw [mem_bset, mem_filter]
    cases d
    · simp only [Bool.false_eq_true, if_false, starts_h hcw hS, cellsOf_sub_h, Xs, mem_product,
        mem_range, mem_univ, and_true, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        have := mem_rectS.mp (hS (h2 0 (by omega)))
        exact ⟨⟨this.1, by omega⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨?_, h3⟩
        have := mem_rectS.mp (hS (h3 k le_rfl))
        omega
    · simp only [if_true, starts_v hcw hS, cellsOf_sub_v, Xs, mem_product,
        mem_range, mem_univ, and_true, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        have := mem_rectS.mp (hS (h2 0 (by omega)))
        exact ⟨⟨by omega, h1⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h2, h3⟩
  rw [sumBits_eq]
  · apply sum_nbij' (fun q => (q / w, q % w, d)) (fun p => idx w p)
    · intro q hq; exact (hmem q).mp hq
    · intro p hp
      have hp' := hp
      rw [mem_filter] at hp
      obtain ⟨hpX, hpd, -⟩ := hp
      obtain ⟨i, j, d'⟩ := p
      simp only at hpd
      subst hpd
      simp only [Xs, mem_product, mem_range, mem_univ, and_true] at hpX
      rw [hmem]
      have e1 : (i * w + j) / w = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt (by omega), zero_add]
      have e2 : (i * w + j) % w = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      simp only [idx, e1, e2]; exact hp'
    · intro q _; simp only [idx]; exact Nat.div_add_mod' q w
    · intro p hp
      rw [mem_filter] at hp
      obtain ⟨hpX, hpd, -⟩ := hp
      obtain ⟨i, j, d'⟩ := p
      simp only at hpd
      subst hpd
      simp only [Xs, mem_product, mem_range, mem_univ, and_true] at hpX
      have e1 : (i * w + j) / w = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt (by omega), zero_add]
      have e2 : (i * w + j) % w = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      simp only [idx, e1, e2]
    · intro q _; simp only [idx, Nat.div_add_mod']
  · calc (bset (starts (bmC w S) (if d = true then w else 1) (k + 1))).card
        ≤ (range (r * w)).card := by
          apply card_le_card
          intro q hq
          rw [hmem, mem_filter] at hq
          simp only [Xs, mem_product, mem_range, mem_univ, and_true] at hq
          rw [mem_range]
          have h1 : (q / w + 1) * w ≤ r * w := Nat.mul_le_mul_right _ (by omega)
          have h2 := Nat.div_add_mod' q w
          have h3 : q % w < w := Nat.mod_lt _ hw0
          rw [add_mul, one_mul] at h1
          omega
      _ = r * w := card_range _

/-- One step of `search`. -/
private theorem search_succ (w N L : ℕ) (f : ℕ → ℕ) (k free lab : ℕ) :
    search w N L f (k + 1) free lab =
      sumBits (fun x => search w N L f k (free - barAt x 1 1 (k + 1))
          (lab + (k + 1) * barAt x L 1 (k + 1))) N (starts free 1 (k + 1)) +
        bif Nat.ble 1 k then
          sumBits (fun x => search w N L f k (free - barAt x 1 w (k + 1))
            (lab + (k + 1) * barAt x L w (k + 1))) N (starts free w (k + 1))
        else 0 := rfl

/-- The base case of `search`. -/
private theorem search_zero (w N L : ℕ) (f : ℕ → ℕ) (free lab : ℕ) :
    search w N L f 0 free lab = bif Nat.beq free 0 then f lab else 0 := rfl

/-- A placement of tile `k + 1` inside `S` fits iff it is not a vertical `1 × 1` tile. -/
private theorem fits_iff {r c : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ rectS r c) {p : Pl} {k : ℕ}
    (hsub : cellsOf p (k + 1) ⊆ S) : Fits r c p (k + 1) ↔ (p.2.2 = true → 1 ≤ k) := by
  obtain ⟨i, j, d⟩ := p
  cases d
  · have := mem_rectS.mp (hS (hsub (mem_cellsOf.mpr
      (show inBar (i, j, false) (k + 1) i (j + k) by simp [inBar]))))
    simp [Fits]; omega
  · have := mem_rectS.mp (hS (hsub (mem_cellsOf.mpr
      (show inBar (i, j, true) (k + 1) (i + k) j by simp [inBar]))))
    simp [Fits]; omega

open Classical in
/-- **The search, made explicit**: `search` sums `f` of the final labelling over the
assignments of placements to the tiles `1, …, k` that partition the free cells. -/
private theorem search_eq {r c w L : ℕ} (hcw : c < w) (f : ℕ → ℕ) :
    ∀ (k : ℕ) (S : Finset (ℕ × ℕ)), S ⊆ rectS r c → ∀ lab : ℕ,
      search w (r * w) L f k (bmC w S) lab =
        ∑ P ∈ Univ r c k, if ValidOn r c k P S then f (lab + enc w L P k) else 0
  | 0, S, hS, lab => by
      rw [search_zero]
      simp only [Univ, sum_singleton, enc, add_zero]
      have hv : ValidOn r c 0 (fun _ => dflt) S ↔ S = ∅ := by
        constructor
        · rintro ⟨-, -, h3, -⟩
          ext ⟨a, b⟩
          simp only [Finset.notMem_empty, iff_false]
          intro hab
          obtain ⟨k', h1, h2, -⟩ := h3 a b hab
          omega
        · rintro rfl
          exact ⟨fun k' h1 h2 => by omega, fun k' a b h1 h2 => by omega,
            fun a b h => by simp at h, fun a b k1 k2 h1 h2 => by omega⟩
      by_cases hS0 : S = ∅
      · have hb : Nat.beq (bmC w S) 0 = true := by
          rw [bmC_eq_zero.mpr hS0]; rfl
        rw [hb, if_pos (hv.mpr hS0)]; rfl
      · have hb : Nat.beq (bmC w S) 0 = false := by
          cases h : Nat.beq (bmC w S) 0
          · rfl
          · exact absurd (bmC_eq_zero.mp (Nat.eq_of_beq_eq_true h)) hS0
        rw [hb, if_neg (fun h => hS0 (hv.mp h))]; rfl
  | k + 1, S, hS, lab => by
      have hw1 : 1 ≤ w := by omega
      have hR : (∑ P ∈ Univ r c (k + 1), if ValidOn r c (k + 1) P S then
            f (lab + enc w L P (k + 1)) else 0) =
          ∑ p ∈ (Xs r c).filter (fun p => Fits r c p (k + 1) ∧ cellsOf p (k + 1) ⊆ S),
            search w (r * w) L f k (bmC w (S \ cellsOf p (k + 1)))
              (lab + (k + 1) * barAt (2 ^ idx w p) L (step w p) (k + 1)) := by
        rw [sum_Univ_succ, sum_comm, sum_filter]
        apply sum_congr rfl
        intro p hp
        split_ifs with hc
        · rw [search_eq hcw f k _ (sdiff_subset.trans hS)]
          apply sum_congr rfl
          intro P hP
          have e1 : ValidOn r c (k + 1) (Function.update P (k + 1) p) S ↔
              ValidOn r c k P (S \ cellsOf p (k + 1)) := by
            rw [validOn_succ, Function.update_self]
            rw [validOn_congr (Q := P) (fun k' h1 h2 => Function.update_of_ne (by omega) _ _)]
            tauto
          have e2 : enc w L (Function.update P (k + 1) p) (k + 1) =
              enc w L P k + (k + 1) * barAt (2 ^ idx w p) L (step w p) (k + 1) := by
            simp only [enc, Function.update_self]
            rw [enc_congr (P := Function.update P (k + 1) p) (Q := P) k
              (fun k' h1 h2 => Function.update_of_ne (by omega) _ _)]
          rw [if_congr e1 rfl rfl, e2, add_comm (enc w L P k), add_assoc]
        · apply sum_eq_zero
          intro P hP
          rw [validOn_succ, Function.update_self, if_neg]
          tauto
      rw [hR, search_succ, ← sum_filter_add_sum_filter_not _ (fun p : Pl => p.2.2 = false)]
      congr 1
      · have h1 := sumBits_starts hcw hS k false (fun x => search w (r * w) L f k
          (bmC w S - barAt x 1 1 (k + 1)) (lab + (k + 1) * barAt x L 1 (k + 1)))
        simp only [Bool.false_eq_true, if_false] at h1
        rw [h1, filter_filter]
        apply sum_congr
        · ext p
          simp only [mem_filter]
          constructor
          · rintro ⟨hpX, hpd, hsub⟩
            refine ⟨hpX, ⟨(fits_iff hS hsub).mpr (by simp [hpd]), hsub⟩, hpd⟩
          · rintro ⟨hpX, ⟨-, hsub⟩, hpd⟩
            exact ⟨hpX, hpd, hsub⟩
        · intro p hp
          rw [mem_filter] at hp
          obtain ⟨-, ⟨-, hsub⟩, hpd⟩ := hp
          have hst : step w p = 1 := by simp [step, hpd]
          have hb : barAt (2 ^ idx w p) 1 1 (k + 1) = bmC w (cellsOf p (k + 1)) := by
            have := barAt_cells hw1 (le_refl 1) p (k + 1)
            simp only [hst, one_mul] at this
            exact this
          rw [hst, hb, bmC_sdiff hsub]
      · by_cases hk : k = 0
        · subst hk
          rw [show Nat.ble 1 0 = false from rfl, cond_false]
          symm
          apply sum_eq_zero
          intro p hp
          simp only [mem_filter] at hp
          obtain ⟨⟨-, hf, -⟩, hpd⟩ := hp
          obtain ⟨i, j, d⟩ := p
          cases d
          · simp at hpd
          · simp [Fits] at hf
        · have hb1 : Nat.ble 1 k = true := Nat.ble_eq_true_of_le (by omega)
          rw [hb1, cond_true]
          have h1 := sumBits_starts hcw hS k true (fun x => search w (r * w) L f k
            (bmC w S - barAt x 1 w (k + 1)) (lab + (k + 1) * barAt x L w (k + 1)))
          simp only [if_true] at h1
          rw [h1, filter_filter]
          apply sum_congr
          · ext p
            simp only [mem_filter]
            constructor
            · rintro ⟨hpX, hpd, hsub⟩
              refine ⟨hpX, ⟨(fits_iff hS hsub).mpr (fun _ => by omega), hsub⟩, by simp [hpd]⟩
            · rintro ⟨hpX, ⟨-, hsub⟩, hpd⟩
              exact ⟨hpX, by simpa using hpd, hsub⟩
          · intro p hp
            rw [mem_filter] at hp
            obtain ⟨-, ⟨-, hsub⟩, hpd⟩ := hp
            have hpd' : p.2.2 = true := by simpa using hpd
            have hst : step w p = w := by simp [step, hpd']
            have hb : barAt (2 ^ idx w p) 1 w (k + 1) = bmC w (cellsOf p (k + 1)) := by
              have := barAt_cells hw1 (le_refl 1) p (k + 1)
              simp only [hst, one_mul] at this
              exact this
            rw [hst, hb, bmC_sdiff hsub]

/-! ## Reading the labelling -/

/-- `∑_{p < n} (2 ^ L - 1) 2 ^ (L p) + 1 = 2 ^ (L n)`. -/
private theorem geom_bound (L : ℕ) : ∀ n, ∑ p ∈ range n, (2 ^ L - 1) * 2 ^ (L * p) + 1 = 2 ^ (L * n)
  | 0 => by simp
  | n + 1 => by
      rw [sum_range_succ, add_right_comm, geom_bound L n]
      have h1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      have e : 2 ^ (L * (n + 1)) = 2 ^ L * 2 ^ (L * n) := by rw [← pow_add]; ring_nf
      rw [e, Nat.sub_mul, one_mul]
      have : 2 ^ (L * n) ≤ 2 ^ L * 2 ^ (L * n) := Nat.le_mul_of_pos_left _ (by positivity)
      omega

/-- `field` as division and remainder. -/
private theorem field_eq (L X p : ℕ) : field L X p = X / 2 ^ (L * p) % 2 ^ L := by
  simp only [field, Nat.land_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
    Nat.and_two_pow_sub_one_eq_mod]

/-- Reading one field of a sum of fields. -/
private theorem field_sum {L : ℕ} (T : Finset ℕ) (v : ℕ → ℕ) (hv : ∀ p ∈ T, v p < 2 ^ L)
    {p0 : ℕ} (hp0 : p0 ∈ T) : field L (∑ p ∈ T, v p * 2 ^ (L * p)) p0 = v p0 := by
  rw [field_eq]
  rw [← sum_filter_add_sum_filter_not T (fun p => p < p0)]
  have hT : T.filter (fun p => ¬ p < p0) = insert p0 (T.filter (fun p => p0 < p)) := by
    ext p; simp only [mem_filter, mem_insert]; constructor
    · rintro ⟨h1, h2⟩; by_cases e : p = p0
      · left; exact e
      · right; exact ⟨h1, by omega⟩
    · rintro (h | ⟨h1, h2⟩)
      · subst h; exact ⟨hp0, by omega⟩
      · exact ⟨h1, by omega⟩
  rw [hT, sum_insert (by simp)]
  -- the low part
  set A := ∑ p ∈ T.filter (fun p => p < p0), v p * 2 ^ (L * p) with hA
  have hAlt : A < 2 ^ (L * p0) := by
    have h1 : A ≤ ∑ p ∈ range p0, (2 ^ L - 1) * 2 ^ (L * p) := by
      calc A ≤ ∑ p ∈ T.filter (fun p => p < p0), (2 ^ L - 1) * 2 ^ (L * p) := by
            apply sum_le_sum
            intro p hp
            have := hv p (mem_filter.mp hp).1
            exact Nat.mul_le_mul_right _ (by omega)
        _ ≤ ∑ p ∈ range p0, (2 ^ L - 1) * 2 ^ (L * p) := by
            apply sum_le_sum_of_subset
            intro p hp; simp only [mem_filter] at hp; simp [hp.2]
    have h2 := geom_bound L p0
    omega
  -- the high part
  have hdvd : 2 ^ (L * p0) * 2 ^ L ∣ ∑ p ∈ T.filter (fun p => p0 < p), v p * 2 ^ (L * p) := by
    apply dvd_sum
    intro p hp
    have h1 : p0 < p := (mem_filter.mp hp).2
    apply Dvd.dvd.mul_left
    rw [← pow_add]
    exact Nat.pow_dvd_pow 2 (by nlinarith)
  obtain ⟨B, hB⟩ := hdvd
  rw [hB]
  have e : A + (v p0 * 2 ^ (L * p0) + 2 ^ (L * p0) * 2 ^ L * B) =
      A + 2 ^ (L * p0) * (v p0 + 2 ^ L * B) := by ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hAlt, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hv p0 hp0)]

open Classical in
/-- The label of cell `x`: the length of the tile covering it. -/
private noncomputable def lbl (k : ℕ) (P : ℕ → Pl) (x : ℕ × ℕ) : ℕ :=
  ∑ k' ∈ Icc 1 k, if inBar (P k') k' x.1 x.2 then k' else 0

open Classical in
/-- The labelling built along a partition of `S` writes the label of each cell of `S` in its
field. -/
private theorem enc_formula {r c w L : ℕ} (hcw : c < w) (hL : 1 ≤ L) {P : ℕ → Pl} :
    ∀ (k : ℕ) (S : Finset (ℕ × ℕ)), S ⊆ rectS r c → ValidOn r c k P S →
      enc w L P k = ∑ x ∈ S, lbl k P x * 2 ^ (L * (x.1 * w + x.2))
  | 0, S, hS, hV => by
      have : S = ∅ := by
        ext ⟨a, b⟩
        simp only [Finset.notMem_empty, iff_false]
        intro hab
        obtain ⟨k', h1, h2, -⟩ := hV.2.2.1 a b hab
        omega
      subst this; simp [enc]
  | k + 1, S, hS, hV => by
      have hw1 : 1 ≤ w := by omega
      obtain ⟨-, hsub, hV'⟩ := validOn_succ.mp hV
      rw [enc, enc_formula hcw hL k _ (sdiff_subset.trans hS) hV', barAt_cells hw1 hL, mul_sum]
      rw [← sum_sdiff hsub]
      congr 1
      · apply sum_congr rfl
        intro x hx
        rw [mem_sdiff] at hx
        obtain ⟨a, b⟩ := x
        have hn : ¬ inBar (P (k + 1)) (k + 1) a b := fun h => hx.2 (mem_cellsOf.mpr h)
        simp only [lbl]
        rw [sum_Icc_succ_top (by omega), if_neg hn, add_zero]
      · apply sum_congr rfl
        intro x hx
        obtain ⟨a, b⟩ := x
        have hy : inBar (P (k + 1)) (k + 1) a b := mem_cellsOf.mp hx
        simp only [lbl]
        rw [sum_Icc_succ_top (by omega), if_pos hy, sum_eq_zero, zero_add]
        intro k' hk'
        rw [mem_Icc] at hk'
        rw [if_neg]
        intro h
        have := hV'.2.1 k' a b hk'.1 hk'.2 h
        exact (mem_sdiff.mp this).2 hx

/-- In a partition, the label of a cell is the length of the tile covering it. -/
private theorem lbl_eq {r c n : ℕ} {P : ℕ → Pl} {S : Finset (ℕ × ℕ)} (hV : ValidOn r c n P S)
    {a b k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n) (hin : inBar (P k) k a b) : lbl n P (a, b) = k := by
  classical
  simp only [lbl]
  rw [sum_eq_single k]
  · simp [hin]
  · intro k' hk' hne
    rw [mem_Icc] at hk'
    rw [if_neg]
    intro h
    exact hne (hV.2.2.2 a b k' k hk'.1 hk'.2 hk1 hk2 h hin)
  · intro h; exact absurd (mem_Icc.mpr ⟨hk1, hk2⟩) h

/-- In a tiling, the field of cell `(a, b)` of the labelling is the length of its tile. -/
private theorem field_cell {r c w n : ℕ} (hcw : c < w) (hn : 1 ≤ n) {P : ℕ → Pl}
    (hV : Valid r c n P) {a b k : ℕ} (hab : a < r ∧ b < c) (hk1 : 1 ≤ k) (hk2 : k ≤ n)
    (hin : inBar (P k) k a b) : field n (enc w n P n) (a * w + b) = k := by
  have hw0 : 0 < w := by omega
  rw [enc_formula hcw hn n _ (subset_refl _) hV]
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * w + x.2) (rectS r c : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hx' := mem_rectS.mp (show (x.1, x.2) ∈ rectS r c from hx)
    have hy' := mem_rectS.mp (show (y.1, y.2) ∈ rectS r c from hy)
    obtain ⟨e1, e2⟩ := idx_inj (by omega) (by omega) hxy
    exact Prod.ext e1 e2
  have hre : ∑ x ∈ rectS r c, lbl n P x * 2 ^ (n * (x.1 * w + x.2)) =
      ∑ q ∈ (rectS r c).image (fun x => x.1 * w + x.2), lbl n P (q / w, q % w) * 2 ^ (n * q) := by
    rw [sum_image hinj]
    apply sum_congr rfl
    intro x hx
    obtain ⟨x1, x2⟩ := x
    have hx' := mem_rectS.mp hx
    have e1 : (x1 * w + x2) / w = x1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt (by omega), zero_add]
    have e2 : (x1 * w + x2) % w = x2 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp only [e1, e2]
  rw [hre, field_sum]
  · have e1 : (a * w + b) / w = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt (by omega), zero_add]
    have e2 : (a * w + b) % w = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [e1, e2, lbl_eq hV hk1 hk2 hin]
  · intro q hq
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
    obtain ⟨x1, x2⟩ := x
    have hx' := mem_rectS.mp hx
    have e1 : (x1 * w + x2) / w = x1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt (by omega), zero_add]
    have e2 : (x1 * w + x2) % w = x2 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp only [e1, e2]
    obtain ⟨k', h1, h2, h3⟩ := hV.2.2.1 x1 x2 hx
    rw [lbl_eq hV h1 h2 h3]
    exact lt_of_le_of_lt h2 Nat.lt_two_pow_self
  · exact mem_image.mpr ⟨(a, b), mem_rectS.mpr hab, rfl⟩

/-! ## No tiling has a non-trivial symmetry -/

/-- A conjunction over `j < n` written with the recursor gives each conjunct. -/
private theorem rec_and {F : ℕ → Bool} : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun j ih => F j && ih) n = true → ∀ j < n, F j = true
  | 0, _ => fun j hj => absurd hj (by omega)
  | n + 1, h => by
      have h' : (F n && Nat.rec (motive := fun _ => Bool) true (fun j ih => F j && ih) n) = true :=
        h
      rw [Bool.and_eq_true] at h'
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · exact rec_and n h'.2 j hj
      · subst hj; exact h'.1

/-- If `g` fixes the labelling, then the labels of `(i, j)` and `g (i, j)` agree. -/
private theorem fixes_imp {r c w L : ℕ} {g : ℕ × ℕ → ℕ × ℕ} {lab : ℕ}
    (h : fixes r c w L g lab = true) (i j : ℕ) (hi : i < r) (hj : j < c) :
    field L lab ((g (i, j)).1 * w + (g (i, j)).2) = field L lab (i * w + j) := by
  have h1 := rec_and (F := fun i => Nat.rec (motive := fun _ => Bool) true
    (fun j ihj => Nat.beq (field L lab ((g (i, j)).1 * w + (g (i, j)).2))
      (field L lab (i * w + j)) && ihj) c) r h i hi
  have h2 := rec_and (F := fun j => Nat.beq (field L lab ((g (i, j)).1 * w + (g (i, j)).2))
    (field L lab (i * w + j))) c h1 j hj
  exact Nat.eq_of_beq_eq_true h2

/-- A bar that covers the cells `(0, b)` and `(r - 1, b)` is the vertical bar of length `r` in
column `b`. -/
private theorem vert_full {r c : ℕ} {p : Pl} {k b : ℕ} (hr : 2 ≤ r) (hf : Fits r c p k)
    (h1 : inBar p k 0 b) (h2 : inBar p k (r - 1) b) : p.2.1 = b ∧ k = r := by
  obtain ⟨i, j, d⟩ := p
  cases d <;> simp only [Fits, inBar, Bool.false_eq_true, if_false, if_true] at hf h1 h2 <;>
    simp only <;> omega

/-- A bar that covers the cells `(a, 0)` and `(a, c - 1)` is the horizontal bar of length `c`
in row `a`. -/
private theorem horiz_full {r c : ℕ} {p : Pl} {k a : ℕ} (hc : 2 ≤ c) (hf : Fits r c p k)
    (h1 : inBar p k a 0) (h2 : inBar p k a (c - 1)) : p.1 = a ∧ k = c := by
  obtain ⟨i, j, d⟩ := p
  cases d <;> simp only [Fits, inBar, Bool.false_eq_true, if_false, if_true] at hf h1 h2 <;>
    simp only <;> omega

/-- No bar covers two opposite corners of the rectangle. -/
private theorem not_diag {r c : ℕ} {p : Pl} {k : ℕ} (hr : 2 ≤ r) (hc : 2 ≤ c)
    (h1 : inBar p k 0 0) (h2 : inBar p k (r - 1) (c - 1)) : False := by
  obtain ⟨i, j, d⟩ := p
  cases d <;> simp only [inBar, Bool.false_eq_true, if_false, if_true] at h1 h2 <;> omega

/-- **No symmetry.** For a non-square rectangle with at least two rows and columns, no
non-identity symmetry fixes a tiling: it would map each tile to the tile of the same length, i.e.
to itself, so two corners swapped by it would lie in one tile, which is impossible for the
half-turn and would give the same full-length tile at both ends for a reflection. -/
private theorem stabCount_eq_one {r c w n : ℕ} (hcw : c < w) (hn : 1 ≤ n) (hr : 2 ≤ r)
    (hc : 2 ≤ c) (hrc : r ≠ c) {P : ℕ → Pl} (hV : Valid r c n P) :
    stabCount r c w n (enc w n P n) = 1 := by
  have cover : ∀ a b, a < r → b < c → ∃ k', 1 ≤ k' ∧ k' ≤ n ∧ inBar (P k') k' a b :=
    fun a b ha hb => hV.2.2.1 a b (mem_rectS.mpr ⟨ha, hb⟩)
  obtain ⟨k1, a1, b1, c1⟩ := cover 0 0 (by omega) (by omega)
  obtain ⟨k2, a2, b2, c2⟩ := cover (r - 1) 0 (by omega) (by omega)
  obtain ⟨k3, a3, b3, c3⟩ := cover 0 (c - 1) (by omega) (by omega)
  obtain ⟨k4, a4, b4, c4⟩ := cover (r - 1) (c - 1) (by omega) (by omega)
  have f1 := field_cell hcw hn hV ⟨by omega, by omega⟩ a1 b1 c1
  have f2 := field_cell hcw hn hV ⟨by omega, by omega⟩ a2 b2 c2
  have f3 := field_cell hcw hn hV ⟨by omega, by omega⟩ a3 b3 c3
  have f4 := field_cell hcw hn hV ⟨by omega, by omega⟩ a4 b4 c4
  simp only [zero_mul, zero_add, add_zero] at f1 f2 f3 f4
  have fit := hV.1
  have e1 : fixes r c w n (fun p => (r - 1 - p.1, p.2)) (enc w n P n) = false := by
    by_contra hcon
    rw [Bool.not_eq_false] at hcon
    have h1 := fixes_imp hcon 0 0 (by omega) (by omega)
    have h2 := fixes_imp hcon 0 (c - 1) (by omega) (by omega)
    simp only [Nat.sub_zero, zero_mul, zero_add, add_zero] at h1 h2
    rw [f1, f2] at h1
    rw [f3, f4] at h2
    subst h1 h2
    obtain ⟨g1, g2⟩ := vert_full hr (fit k2 a2 b2) c1 c2
    obtain ⟨g3, g4⟩ := vert_full hr (fit k4 a4 b4) c3 c4
    have : k2 = k4 := by omega
    subst this
    omega
  have e2 : fixes r c w n (fun p => (p.1, c - 1 - p.2)) (enc w n P n) = false := by
    by_contra hcon
    rw [Bool.not_eq_false] at hcon
    have h1 := fixes_imp hcon 0 0 (by omega) (by omega)
    have h2 := fixes_imp hcon (r - 1) 0 (by omega) (by omega)
    simp only [Nat.sub_zero, zero_mul, zero_add, add_zero] at h1 h2
    rw [f1, f3] at h1
    rw [f2, f4] at h2
    subst h1 h2
    obtain ⟨g1, g2⟩ := horiz_full hc (fit k3 a3 b3) c1 c3
    obtain ⟨g3, g4⟩ := horiz_full hc (fit k4 a4 b4) c2 c4
    have : k3 = k4 := by omega
    subst this
    omega
  have e3 : fixes r c w n (fun p => (r - 1 - p.1, c - 1 - p.2)) (enc w n P n) = false := by
    by_contra hcon
    rw [Bool.not_eq_false] at hcon
    have h1 := fixes_imp hcon 0 0 (by omega) (by omega)
    simp only [Nat.sub_zero, zero_mul, add_zero] at h1
    rw [f1, f4] at h1
    subst h1
    exact not_diag hr hc c1 c4
  simp only [stabCount, otherSymmetries, if_neg hrc, List.append_nil, e1, e2, e3, cond_false]

/-- `∑_{b < c} 2 ^ b = 2 ^ c - 1`. -/
private theorem sum_two_pow (c : ℕ) : ∑ b ∈ range c, 2 ^ b = 2 ^ c - 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [sum_range_succ, ih, pow_succ]
      have := Nat.one_le_two_pow (n := c)
      omega

/-- `rectMask` is the bitmask of the rectangle. -/
private theorem rectMask_eq (r c w : ℕ) : rectMask r c w = bmC w (rectS r c) := by
  induction r with
  | zero => simp [rectMask, bmC, rectS]
  | succ r ih =>
      show rectMask r c w + (2 ^ c - 1) * 2 ^ (r * w) = _
      rw [ih]
      simp only [bmC, rectS, sum_product, sum_range_succ]
      congr 1
      simp only [pow_add, ← mul_sum, sum_two_pow]
      ring

open Classical in
/-- **The definition, made explicit.** For a non-square rectangle with at least two rows and
columns, the value computed by `a` is the number of tilings divided by `4`. -/
private theorem search_count {r c n : ℕ} (hn : 1 ≤ n) (hr : 2 ≤ r) (hc : 2 ≤ c) (hrc : r ≠ c) :
    search (c + 1) (r * (c + 1)) n (stabCount r c (c + 1) n) n (rectMask r c (c + 1)) 0 /
      (1 + (otherSymmetries r c).length) = ((Univ r c n).filter (Valid r c n)).card / 4 := by
  have hlen : (otherSymmetries r c).length = 3 := by simp [otherSymmetries, hrc]
  rw [hlen, rectMask_eq, search_eq (by omega) _ n _ (subset_refl _) 0]
  congr 1
  rw [card_filter]
  apply sum_congr rfl
  intro P _
  by_cases h : Valid r c n P
  · have h' : ValidOn r c n P (rectS r c) := h
    rw [if_pos h, if_pos h', zero_add, stabCount_eq_one (by omega) hn hr hc hrc h]
  · have h' : ¬ ValidOn r c n P (rectS r c) := h
    rw [if_neg h, if_neg h']

/-! ## Tilings: general facts -/

/-- Membership in a horizontal bar. -/
private theorem inBar_h {p : Pl} (hd : p.2.2 = false) {k a b : ℕ} :
    inBar p k a b ↔ a = p.1 ∧ p.2.1 ≤ b ∧ b < p.2.1 + k := by
  simp [inBar, hd]

/-- Membership in a vertical bar. -/
private theorem inBar_v {p : Pl} (hd : p.2.2 = true) {k a b : ℕ} :
    inBar p k a b ↔ b = p.2.1 ∧ p.1 ≤ a ∧ a < p.1 + k := by
  simp [inBar, hd]

/-- A horizontal bar fits. -/
private theorem fits_h {r c : ℕ} {p : Pl} (hd : p.2.2 = false) {k : ℕ} :
    Fits r c p k ↔ p.1 < r ∧ p.2.1 + k ≤ c := by
  simp [Fits, hd]

/-- A vertical bar fits. -/
private theorem fits_v {r c : ℕ} {p : Pl} (hd : p.2.2 = true) {k : ℕ} :
    Fits r c p k ↔ p.1 + k ≤ r ∧ p.2.1 < c ∧ 2 ≤ k := by
  simp [Fits, hd]

/-- In a tiling every tile fits. -/
private theorem vfit {r c n : ℕ} {P : ℕ → Pl} (hV : Valid r c n P) {k : ℕ} (h1 : 1 ≤ k)
    (h2 : k ≤ n) : Fits r c (P k) k := hV.1 k h1 h2

/-- In a tiling every cell is covered. -/
private theorem vcover {r c n : ℕ} {P : ℕ → Pl} (hV : Valid r c n P) {a b : ℕ} (ha : a < r)
    (hb : b < c) : ∃ k, 1 ≤ k ∧ k ≤ n ∧ inBar (P k) k a b :=
  hV.2.2.1 a b (mem_rectS.mpr ⟨ha, hb⟩)

/-- In a tiling no cell is covered twice. -/
private theorem vdisj {r c n : ℕ} {P : ℕ → Pl} (hV : Valid r c n P) {a b k1 k2 : ℕ}
    (h1 : 1 ≤ k1) (h2 : k1 ≤ n) (h3 : 1 ≤ k2) (h4 : k2 ≤ n)
    (hin1 : inBar (P k1) k1 a b) (hin2 : inBar (P k2) k2 a b) : k1 = k2 :=
  hV.2.2.2 a b k1 k2 h1 h2 h3 h4 hin1 hin2

/-- A tiling from fitting, covering and disjointness. -/
private theorem valid_of {r c n : ℕ} {P : ℕ → Pl}
    (hfit : ∀ k, 1 ≤ k → k ≤ n → Fits r c (P k) k)
    (hcov : ∀ a b, a < r → b < c → ∃ k, 1 ≤ k ∧ k ≤ n ∧ inBar (P k) k a b)
    (hdisj : ∀ a b k1 k2, 1 ≤ k1 → k1 ≤ n → 1 ≤ k2 → k2 ≤ n →
      inBar (P k1) k1 a b → inBar (P k2) k2 a b → k1 = k2) :
    Valid r c n P :=
  ⟨hfit, fun k _a _b h1 h2 hin => mem_rectS.mpr (inBar_lt (hfit k h1 h2) hin),
    fun a b hab => hcov a b (mem_rectS.mp hab).1 (mem_rectS.mp hab).2, hdisj⟩

/-- A valid normalized assignment lies in `Univ`. -/
private theorem mem_Univ_of {r c n : ℕ} {P : ℕ → Pl} (hV : Valid r c n P)
    (hn : ∀ k, (k = 0 ∨ n < k) → P k = dflt) : P ∈ Univ r c n := by
  rw [mem_Univ]
  refine ⟨hn, fun k h1 h2 => ?_⟩
  have hf := vfit hV h1 h2
  simp only [Xs, mem_product, mem_range, mem_univ, and_true]
  rcases hd : (P k).2.2 with _ | _
  · rw [fits_h hd] at hf; omega
  · rw [fits_v hd] at hf; omega

/-- Pigeonhole: an injection of `R` consecutive tiles into `R` rows hits every row. -/
private theorem pigeon {R lo : ℕ} (f : ℕ → ℕ) (hf : ∀ k, lo ≤ k → k < lo + R → f k < R)
    (hinj : ∀ k k', lo ≤ k → k < lo + R → lo ≤ k' → k' < lo + R → f k = f k' → k = k') :
    ∀ a < R, ∃ k, lo ≤ k ∧ k < lo + R ∧ f k = a := by
  classical
  intro a ha
  have hsub : (Finset.Ico lo (lo + R)).image f ⊆ Finset.range R := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    rw [mem_Ico] at hk
    exact mem_range.mpr (hf k hk.1 hk.2)
  have hcard : ((Finset.Ico lo (lo + R)).image f).card = R := by
    rw [card_image_of_injOn]
    · simp
    · intro x hx y hy hxy
      simp only [coe_Ico, Set.mem_Ico] at hx hy
      exact hinj x y hx.1 hx.2 hy.1 hy.2 hxy
  have heq := eq_of_subset_of_card_le hsub (by rw [hcard, card_range])
  have : a ∈ (Finset.Ico lo (lo + R)).image f := by rw [heq]; exact mem_range.mpr ha
  obtain ⟨k, hk, rfl⟩ := mem_image.mp this
  rw [mem_Ico] at hk
  exact ⟨k, hk.1, hk.2, rfl⟩

/-- If `R` tiles are horizontal and all cross column `x`, every row holds one of them. -/
private theorem rows_cover {R C N : ℕ} {P : ℕ → Pl} (hV : Valid R C N P) {lo x : ℕ}
    (hlo : 1 ≤ lo) (hN : lo + R ≤ N + 1)
    (hlong : ∀ k, lo ≤ k → k < lo + R →
      (P k).2.2 = false ∧ (P k).2.1 ≤ x ∧ x < (P k).2.1 + k) :
    ∀ a < R, ∃ k, lo ≤ k ∧ k < lo + R ∧ (P k).1 = a := by
  apply pigeon (fun k => (P k).1)
  · intro k h1 h2
    have hf := vfit hV (by omega) (show k ≤ N by omega)
    rw [fits_h (hlong k h1 h2).1] at hf
    exact hf.1
  · intro k k' h1 h2 h3 h4 he
    obtain ⟨d1, e1, f1⟩ := hlong k h1 h2
    obtain ⟨d2, e2, f2⟩ := hlong k' h3 h4
    have he' : (P k).1 = (P k').1 := he
    exact vdisj hV (a := (P k).1) (b := x) (by omega) (by omega) (by omega) (by omega)
      (by rw [inBar_h d1]; omega) (by rw [inBar_h d2]; omega)

/-- Tiles `≤ m` avoid a column all of whose cells lie in tiles `> m`. -/
private theorem avoid_of_cover {R C N : ℕ} {P : ℕ → Pl} (hV : Valid R C N P) {m x : ℕ}
    (hmN : m ≤ N) (hx : ∀ a < R, ∃ K, m < K ∧ K ≤ N ∧ inBar (P K) K a x) :
    ∀ k, 1 ≤ k → k ≤ m → ∀ a b, inBar (P k) k a b → b ≠ x := by
  intro k h1 h2 a b hin hb
  subst hb
  have hlt := inBar_lt (vfit hV h1 (show k ≤ N by omega)) hin
  obtain ⟨K, hK1, hK2, hK⟩ := hx a hlt.1
  have := vdisj hV h1 (show k ≤ N by omega) (by omega) hK2 hin hK
  omega

/-- A horizontal bar avoiding column `x` lies entirely to its left or to its right. -/
private theorem avoid_h {p : Pl} {k x : ℕ} (hd : p.2.2 = false)
    (h : ∀ a b, inBar p k a b → b ≠ x) : p.2.1 + k ≤ x ∨ x < p.2.1 := by
  by_contra hc
  exact h p.1 x (by rw [inBar_h hd]; omega) rfl

/-- A vertical bar avoiding column `x` is not in column `x`. -/
private theorem avoid_v {p : Pl} {k x : ℕ} (hd : p.2.2 = true) (hk : 1 ≤ k)
    (h : ∀ a b, inBar p k a b → b ≠ x) : p.2.1 ≠ x := by
  intro e
  exact h p.1 p.2.1 (by rw [inBar_v hd]; omega) e

/-! ## Structure of the tilings of `(m + 1) × (2m + 1)` (tiles up to `2m + 1`) -/

/-- In a tiling of `(m + 1) × (2m + 1)`, tile `2m + 1` is a full row. -/
private theorem s_top {m : ℕ} (hm : 1 ≤ m) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q) :
    (Q (2 * m + 1)).2.2 = false ∧ (Q (2 * m + 1)).2.1 = 0 := by
  have hf := vfit hQ (k := 2 * m + 1) (by omega) le_rfl
  rcases hd : (Q (2 * m + 1)).2.2 with _ | _
  · rw [fits_h hd] at hf; exact ⟨rfl, by omega⟩
  · rw [fits_v hd] at hf; omega

/-- In a tiling of `(m + 1) × (2m + 1)`, the tiles `m + 1, …, 2m + 1` are horizontal and cross the
middle column `m`. -/
private theorem s_long {m : ℕ} (hm : 1 ≤ m) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q) :
    ∀ k, m + 1 ≤ k → k ≤ 2 * m + 1 →
      (Q k).2.2 = false ∧ (Q k).2.1 ≤ m ∧ m < (Q k).2.1 + k := by
  intro k h1 h2
  have hf := vfit hQ (k := k) (by omega) h2
  rcases hd : (Q k).2.2 with _ | _
  · rw [fits_h hd] at hf; exact ⟨rfl, by omega, by omega⟩
  · rw [fits_v hd] at hf
    exfalso
    obtain ⟨t1, t2⟩ := s_top hm hQ
    have ht := vfit hQ (k := 2 * m + 1) (by omega) le_rfl
    rw [fits_h t1] at ht
    have := vdisj hQ (a := (Q (2 * m + 1)).1) (b := (Q k).2.1) (k1 := k) (k2 := 2 * m + 1)
      (by omega) h2 (by omega) le_rfl (by rw [inBar_v hd]; omega) (by rw [inBar_h t1]; omega)
    omega

/-- In a tiling of `(m + 1) × (2m + 1)`, every row holds one of the tiles `m + 1, …, 2m + 1`. -/
private theorem s_rows {m : ℕ} (hm : 1 ≤ m) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q) :
    ∀ a < m + 1, ∃ k, m + 1 ≤ k ∧ k < m + 1 + (m + 1) ∧ (Q k).1 = a :=
  rows_cover hQ (lo := m + 1) (x := m) (by omega) (by omega)
    (fun k h1 h2 => s_long hm hQ k h1 (by omega))

/-- A placement of length `k` avoiding column `m`. -/
private def AvM (m : ℕ) (q : Pl) (k : ℕ) : Prop :=
  (q.2.2 = false → q.2.1 + k ≤ m ∨ m < q.2.1) ∧ (q.2.2 = true → q.2.1 ≠ m)

/-- In a tiling of `(m + 1) × (2m + 1)`, the tiles `1, …, m` avoid the middle column `m`. -/
private theorem s_avm {m : ℕ} (hm : 1 ≤ m) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q) :
    ∀ k, 1 ≤ k → k ≤ m → AvM m (Q k) k := by
  have hcov : ∀ a < m + 1, ∃ K, m < K ∧ K ≤ 2 * m + 1 ∧ inBar (Q K) K a m := by
    intro a ha
    obtain ⟨K, h1, h2, h3⟩ := s_rows hm hQ a ha
    obtain ⟨d, e, f⟩ := s_long hm hQ K h1 (by omega)
    exact ⟨K, by omega, by omega, by rw [inBar_h d]; omega⟩
  have hav := avoid_of_cover hQ (by omega) hcov
  intro k h1 h2
  refine ⟨fun hd => avoid_h hd (hav k h1 h2), fun hd => avoid_v hd h1 (hav k h1 h2)⟩

/-- In a tiling of `(m + 1) × (2m + 1)`, tile `2m` is horizontal, starts in column `0` or `1` and
lies in another row than tile `2m + 1`. -/
private theorem s_two {m : ℕ} (hm : 1 ≤ m) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q) :
    (Q (2 * m)).2.2 = false ∧ (Q (2 * m)).2.1 ≤ 1 ∧ (Q (2 * m)).1 ≠ (Q (2 * m + 1)).1 := by
  obtain ⟨d1, e1, f1⟩ := s_long hm hQ (2 * m) (by omega) (by omega)
  obtain ⟨d2, e2, f2⟩ := s_long hm hQ (2 * m + 1) (by omega) le_rfl
  have hf := vfit hQ (k := 2 * m) (by omega) (by omega)
  rw [fits_h d1] at hf
  refine ⟨d1, by omega, fun he => ?_⟩
  have := vdisj hQ (a := (Q (2 * m)).1) (b := m) (k1 := 2 * m) (k2 := 2 * m + 1)
    (by omega) (by omega) (by omega) le_rfl (by rw [inBar_h d1]; omega)
    (by rw [inBar_h d2]; omega)
  omega

/-! ## Structure of the tilings of `(m + 1) × (2m + 3)` (tiles up to `2m + 2`) -/

/-- In a tiling of `(m + 1) × (2m + 3)`, the tiles `m + 2, …, 2m + 2` are horizontal and cross the
middle column `m + 1`. -/
private theorem b_long {m : ℕ} {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P) :
    ∀ K, m + 2 ≤ K → K ≤ 2 * m + 2 → (P K).2.2 = false ∧ (P K).2.1 ≤ m + 1 ∧
      m + 1 < (P K).2.1 + K ∧ (P K).2.1 + K ≤ 2 * m + 3 := by
  intro K h1 h2
  have hf := vfit hP (k := K) (by omega) h2
  rcases hd : (P K).2.2 with _ | _
  · rw [fits_h hd] at hf; exact ⟨rfl, by omega, by omega, by omega⟩
  · rw [fits_v hd] at hf; omega

/-- In a tiling of `(m + 1) × (2m + 3)`, every row holds one of the tiles `m + 2, …, 2m + 2`. -/
private theorem b_rows {m : ℕ} {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P) :
    ∀ a < m + 1, ∃ K, m + 2 ≤ K ∧ K < m + 2 + (m + 1) ∧ (P K).1 = a :=
  rows_cover hP (lo := m + 2) (x := m + 1) (by omega) (by omega)
    (fun K h1 h2 => by
      obtain ⟨a, b, c, -⟩ := b_long hP K h1 (by omega)
      exact ⟨a, b, c⟩)

/-- In a tiling of `(m + 1) × (2m + 3)`, a vertical tile `m + 1` is the first or the last column. -/
private theorem b_vert {m : ℕ} (hm : 1 ≤ m) {P : ℕ → Pl}
    (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P) (hd : (P (m + 1)).2.2 = true) :
    P (m + 1) = (0, 0, true) ∨ P (m + 1) = (0, 2 * m + 2, true) := by
  have hf := vfit hP (k := m + 1) (by omega) (by omega)
  rw [fits_v hd] at hf
  obtain ⟨d2, e2, f2, g2⟩ := b_long hP (2 * m + 2) (by omega) le_rfl
  have hf2 := vfit hP (k := 2 * m + 2) (by omega) le_rfl
  rw [fits_h d2] at hf2
  have hno : ¬ ((P (2 * m + 2)).2.1 ≤ (P (m + 1)).2.1 ∧
      (P (m + 1)).2.1 < (P (2 * m + 2)).2.1 + (2 * m + 2)) := by
    intro h
    have := vdisj hP (a := (P (2 * m + 2)).1) (b := (P (m + 1)).2.1) (k1 := m + 1)
      (k2 := 2 * m + 2) (by omega) (by omega) (by omega) le_rfl
      (by rw [inBar_v hd]; omega) (by rw [inBar_h d2]; omega)
    omega
  have h1 : (P (m + 1)).1 = 0 := by omega
  rcases Nat.lt_or_ge (P (m + 1)).2.1 1 with h | h
  · left
    have h2 : (P (m + 1)).2.1 = 0 := by omega
    exact Prod.ext h1 (Prod.ext h2 hd)
  · right
    have h2 : (P (m + 1)).2.1 = 2 * m + 2 := by omega
    exact Prod.ext h1 (Prod.ext h2 hd)

/-- In a tiling of `(m + 1) × (2m + 3)`, a horizontal tile `m + 1` shares its row with tile
`m + 2`, and the two fill that row. -/
private theorem b_horiz {m : ℕ} {P : ℕ → Pl}
    (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P) (hd : (P (m + 1)).2.2 = false) :
    (P (m + 2)).2.2 = false ∧ (P (m + 2)).1 = (P (m + 1)).1 ∧
      (((P (m + 1)).2.1 = 0 ∧ (P (m + 2)).2.1 = m + 1) ∨
        ((P (m + 1)).2.1 = m + 2 ∧ (P (m + 2)).2.1 = 0)) := by
  have hf := vfit hP (k := m + 1) (by omega) (by omega)
  rw [fits_h hd] at hf
  obtain ⟨K, hK1, hK2, hK3⟩ := b_rows hP (P (m + 1)).1 hf.1
  obtain ⟨d, e, f, g⟩ := b_long hP K hK1 (by omega)
  have hno : ∀ b, ¬ ((P (m + 1)).2.1 ≤ b ∧ b < (P (m + 1)).2.1 + (m + 1) ∧
      (P K).2.1 ≤ b ∧ b < (P K).2.1 + K) := by
    intro b h
    have := vdisj hP (a := (P (m + 1)).1) (b := b) (k1 := m + 1) (k2 := K) (by omega)
      (by omega) (by omega) (by omega) (by rw [inBar_h hd]; omega) (by rw [inBar_h d]; omega)
    omega
  have h1 := hno (P (m + 1)).2.1
  have h2 := hno (P K).2.1
  have hK : K = m + 2 := by omega
  subst hK
  exact ⟨d, hK3, by omega⟩

/-! ## Column maps between the two rectangles

Small column `b` goes to big column `cB b`: the big rectangle has `e` extra columns on the left
and `δ` extra columns right after column `m + e`. `cF` goes back (the inserted columns go to the
small column `m`). -/

/-- Small column `j` as a column of the big rectangle. -/
private def cB (m e δ j : ℕ) : ℕ := if j ≤ m then j + e else j + e + δ

/-- Big column `j` as a column of the small rectangle (the inserted columns go to `m`). -/
private def cF (m e δ j : ℕ) : ℕ :=
  if j ≤ m + e then j - e else if j ≤ m + e + δ then m else j - e - δ

/-- A short tile of the small rectangle moved to the big rectangle. -/
private def mvB (m e δ : ℕ) (p : Pl) : Pl := (p.1, cB m e δ p.2.1, p.2.2)

/-- A short tile of the big rectangle moved to the small rectangle. -/
private def mvF (m e δ : ℕ) (p : Pl) : Pl := (p.1, cF m e δ p.2.1, p.2.2)

/-- A long tile of the small rectangle moved (and lengthened) to the big rectangle. -/
private def lgB (e : ℕ) (p : Pl) : Pl := (p.1, p.2.1 + e, false)

/-- A long tile of the big rectangle moved (and shortened) to the small rectangle. -/
private def lgF (e : ℕ) (p : Pl) : Pl := (p.1, p.2.1 - e, false)

/-- A placement of length `k` in the big rectangle avoiding the inserted columns. -/
private def AvD (m e δ : ℕ) (p : Pl) (k : ℕ) : Prop :=
  e ≤ p.2.1 ∧
  (p.2.2 = false → (p.2.1 + k ≤ m + e ∨ m + e + δ < p.2.1) ∧ p.2.1 + k ≤ 2 * m + 1 + e + δ) ∧
  (p.2.2 = true → (p.2.1 < m + e ∨ m + e + δ < p.2.1) ∧ p.2.1 ≤ 2 * m + e + δ)

/-- Membership in a moved short tile, read in the small rectangle. -/
private theorem inBar_mvB {m e δ : ℕ} {q : Pl} {k a b : ℕ} (hq : AvM m q k) (he : e ≤ b) :
    inBar (mvB m e δ q) k a b ↔ inBar q k a (cF m e δ b) := by
  obtain ⟨i, j, d⟩ := q
  unfold AvM at hq
  cases d <;> simp only [mvB, cB, cF, inBar, Bool.false_eq_true, if_false, if_true,
    forall_const] at hq ⊢ <;> split_ifs <;> omega

/-- Membership in a lengthened long tile, read in the small rectangle. -/
private theorem inBar_lgB {m e δ : ℕ} {q : Pl} {k a b : ℕ} (hd : q.2.2 = false)
    (h1 : q.2.1 ≤ m) (h2 : m < q.2.1 + k) (he : e ≤ b) :
    inBar (lgB e q) (k + δ) a b ↔ inBar q k a (cF m e δ b) := by
  rw [inBar_h hd, inBar_h rfl]
  simp only [lgB, cF]
  split_ifs <;> omega

/-- `cF` undoes `cB`. -/
private theorem cF_cB (m e δ b : ℕ) : cF m e δ (cB m e δ b) = b := by
  unfold cF cB; split_ifs <;> omega

/-- `cB` skips the `e` extra columns on the left. -/
private theorem le_cB (m e δ b : ℕ) : e ≤ cB m e δ b := by
  unfold cB; split_ifs <;> omega

/-- A short tile of the big rectangle avoiding the inserted columns moves to one avoiding the
middle column. -/
private theorem avM_mvF {m e δ : ℕ} {p : Pl} {k : ℕ} (hp : AvD m e δ p k) :
    AvM m (mvF m e δ p) k := by
  obtain ⟨i, j, d⟩ := p
  unfold AvD at hp
  unfold AvM
  cases d <;> simp only [mvF, cF, Bool.false_eq_true, Bool.true_eq_false, forall_const,
    and_true, true_and, IsEmpty.forall_iff] at hp ⊢ <;>
    split_ifs <;> omega

/-- `mvB` undoes `mvF` on tiles avoiding the inserted columns. -/
private theorem mvB_mvF {m e δ : ℕ} {p : Pl} {k : ℕ} (hp : AvD m e δ p k) :
    mvB m e δ (mvF m e δ p) = p := by
  obtain ⟨i, j, d⟩ := p
  unfold AvD at hp
  simp only [mvB, mvF, cB, cF, Prod.mk.injEq, true_and, and_true]
  cases d <;> simp only [Bool.false_eq_true, Bool.true_eq_false, forall_const,
    and_true, true_and, IsEmpty.forall_iff] at hp <;> split_ifs <;> omega

/-- `mvF` undoes `mvB`. -/
private theorem mvF_mvB (m e δ : ℕ) (q : Pl) : mvF m e δ (mvB m e δ q) = q := by
  simp only [mvF, mvB, cF_cB]

/-- `lgB` undoes `lgF` on horizontal tiles starting after the `e` extra columns. -/
private theorem lgB_lgF {e : ℕ} {p : Pl} (hd : p.2.2 = false) (he : e ≤ p.2.1) :
    lgB e (lgF e p) = p := by
  obtain ⟨i, j, d⟩ := p
  simp only at hd he
  subst hd
  simp only [lgB, lgF, Prod.mk.injEq, true_and, and_true]
  omega

/-- `lgF` undoes `lgB` on horizontal tiles. -/
private theorem lgF_lgB {e : ℕ} {q : Pl} (hd : q.2.2 = false) : lgF e (lgB e q) = q := by
  obtain ⟨i, j, d⟩ := q
  simp only at hd
  subst hd
  simp [lgB, lgF]

/-- A moved short tile avoids the inserted columns. -/
private theorem avD_mvB {m e δ : ℕ} {q : Pl} {k : ℕ} (hq : AvM m q k)
    (hf : Fits (m + 1) (2 * m + 1) q k) : AvD m e δ (mvB m e δ q) k := by
  obtain ⟨i, j, d⟩ := q
  unfold AvM at hq
  unfold AvD
  cases d <;> simp only [mvB, cB, Fits, Bool.false_eq_true, Bool.true_eq_false, if_false,
    if_true, forall_const, and_true, true_and, IsEmpty.forall_iff] at hq hf ⊢ <;>
    split_ifs <;> omega

/-- A moved short tile fits in the big rectangle. -/
private theorem fits_mvB {m e δ : ℕ} (hed : e + δ ≤ 2) {q : Pl} {k : ℕ} (hq : AvM m q k)
    (hf : Fits (m + 1) (2 * m + 1) q k) : Fits (m + 1) (2 * m + 3) (mvB m e δ q) k := by
  obtain ⟨i, j, d⟩ := q
  unfold AvM at hq
  cases d <;> simp only [mvB, cB, Fits, Bool.false_eq_true, Bool.true_eq_false, if_false,
    if_true, forall_const, and_true, true_and, IsEmpty.forall_iff] at hq hf ⊢ <;>
    split_ifs <;> omega

/-- A moved short tile fits in the small rectangle. -/
private theorem fits_mvF {m e δ : ℕ} {p : Pl} {k : ℕ} (hp : AvD m e δ p k)
    (hf : Fits (m + 1) (2 * m + 3) p k) : Fits (m + 1) (2 * m + 1) (mvF m e δ p) k := by
  obtain ⟨i, j, d⟩ := p
  unfold AvD at hp
  cases d <;> simp only [mvF, cF, Fits, Bool.false_eq_true, Bool.true_eq_false, if_false,
    if_true, forall_const, and_true, true_and, IsEmpty.forall_iff] at hp hf ⊢ <;>
    split_ifs <;> omega

/-- Membership in a moved short tile, read in the big rectangle. -/
private theorem inBar_mvF {m e δ : ℕ} {p : Pl} {k a b : ℕ} (hp : AvD m e δ p k) :
    inBar (mvF m e δ p) k a b ↔ inBar p k a (cB m e δ b) := by
  conv_rhs => rw [← mvB_mvF hp]
  rw [inBar_mvB (avM_mvF hp) (le_cB m e δ b), cF_cB]

/-- Membership in a shortened long tile, read in the big rectangle. -/
private theorem inBar_lgF {m e δ : ℕ} {p : Pl} {k a b : ℕ} (hd : p.2.2 = false)
    (he : e ≤ p.2.1) (h1 : p.2.1 ≤ m + e) (h2 : m + e < p.2.1 + k) :
    inBar (lgF e p) k a b ↔ inBar p (k + δ) a (cB m e δ b) := by
  conv_rhs => rw [← lgB_lgF hd he]
  rw [inBar_lgB (m := m) (δ := δ) rfl (by simp only [lgF]; omega) (by simp only [lgF]; omega)
    (le_cB m e δ b), cF_cB]

/-! ## The two classes of tilings of the big rectangle -/

/-- Class `V`: tile `m + 1` is the vertical bar in column `s` (`s = 0`, `e = 1` or
`s = 2m + 2`, `e = 0`). -/
private theorem bV_long {m e s : ℕ} (hes : (e = 1 ∧ s = 0) ∨ (e = 0 ∧ s = 2 * m + 2))
    {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P)
    (hc : P (m + 1) = (0, s, true)) :
    ∀ K, m + 2 ≤ K → K ≤ 2 * m + 2 → (P K).2.2 = false ∧ e ≤ (P K).2.1 ∧
      (P K).2.1 ≤ m + e ∧ m + e < (P K).2.1 + (K - 1) ∧ (P K).2.1 + K ≤ 2 * m + 2 + e := by
  intro K h1 h2
  obtain ⟨d, e1, f, g⟩ := b_long hP K h1 h2
  have hf := vfit hP (k := K) (by omega) h2
  rw [fits_h d] at hf
  have hno : ¬ ((P K).2.1 ≤ s ∧ s < (P K).2.1 + K) := by
    intro h
    have := vdisj hP (a := (P K).1) (b := s) (k1 := m + 1) (k2 := K) (by omega) (by omega)
      (by omega) h2 (by rw [hc, inBar_v rfl]; simp only [true_and]; omega)
      (by rw [inBar_h d]; omega)
    omega
  refine ⟨d, ?_⟩
  omega

/-- Class `V`: the tiles `1, …, m` avoid the removed columns. -/
private theorem bV_avd {m e s : ℕ} (hes : (e = 1 ∧ s = 0) ∨ (e = 0 ∧ s = 2 * m + 2))
    {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P)
    (hc : P (m + 1) = (0, s, true)) :
    ∀ k, 1 ≤ k → k ≤ m → AvD m e 1 (P k) k := by
  have hlong := bV_long hes hP hc
  have hcol : ∀ x, m + e ≤ x → x ≤ m + 1 + e →
      ∀ a < m + 1, ∃ K, m < K ∧ K ≤ 2 * m + 2 ∧ inBar (P K) K a x := by
    intro x hx1 hx2 a ha
    obtain ⟨K, h1, h2, h3⟩ := b_rows hP a ha
    obtain ⟨d, e1, f, g, -⟩ := hlong K h1 (by omega)
    exact ⟨K, by omega, by omega, by rw [inBar_h d]; omega⟩
  have hs : ∀ a < m + 1, ∃ K, m < K ∧ K ≤ 2 * m + 2 ∧ inBar (P K) K a s := by
    intro a ha
    exact ⟨m + 1, by omega, by omega, by rw [hc, inBar_v rfl]; simp only [true_and]; omega⟩
  have A1 := avoid_of_cover hP (by omega) (hcol (m + e) le_rfl (by omega))
  have A2 := avoid_of_cover hP (by omega) (hcol (m + 1 + e) (by omega) le_rfl)
  have A3 := avoid_of_cover hP (by omega) hs
  intro k h1 h2
  have hf := vfit hP (k := k) h1 (by omega)
  unfold AvD
  rcases hd : (P k).2.2 with _ | _
  · rw [fits_h hd] at hf
    have B1 := avoid_h hd (A1 k h1 h2)
    have B2 := avoid_h hd (A2 k h1 h2)
    have B3 := avoid_h hd (A3 k h1 h2)
    exact ⟨by omega, fun _ => ⟨by omega, by omega⟩, fun h => by simp at h⟩
  · rw [fits_v hd] at hf
    have B1 := avoid_v hd h1 (A1 k h1 h2)
    have B2 := avoid_v hd h1 (A2 k h1 h2)
    have B3 := avoid_v hd h1 (A3 k h1 h2)
    exact ⟨by omega, fun h => by simp at h, fun _ => ⟨by omega, by omega⟩⟩

/-- Class `H`: tile `m + 1` is horizontal, starting in column `u` (`0` or `m + 2`); then tile
`m + 2` fills the rest of its row, from column `v`. -/
private theorem bH_pair {m u v : ℕ} (huv : (u = 0 ∧ v = m + 1) ∨ (u = m + 2 ∧ v = 0))
    {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P)
    (hc : (P (m + 1)).2.2 = false ∧ (P (m + 1)).2.1 = u) :
    (P (m + 2)).2.2 = false ∧ (P (m + 2)).1 = (P (m + 1)).1 ∧ (P (m + 2)).2.1 = v := by
  obtain ⟨d, e, f⟩ := b_horiz hP hc.1
  exact ⟨d, e, by omega⟩

/-- In a tiling of `(m + 1) × (2m + 3)`, the tiles `m + 3, …, 2m + 2` cross the middle columns
`m, m + 1, m + 2`. -/
private theorem bH_long {m : ℕ} {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P) :
    ∀ K, m + 3 ≤ K → K ≤ 2 * m + 2 → (P K).2.2 = false ∧ (P K).2.1 ≤ m ∧
      m < (P K).2.1 + (K - 2) := by
  intro K h1 h2
  obtain ⟨d, e, f, g⟩ := b_long hP K (by omega) h2
  exact ⟨d, by omega, by omega⟩

/-- Class `H`: the tiles `1, …, m` avoid the removed columns. -/
private theorem bH_avd {m u v : ℕ} (huv : (u = 0 ∧ v = m + 1) ∨ (u = m + 2 ∧ v = 0))
    {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P)
    (hc : (P (m + 1)).2.2 = false ∧ (P (m + 1)).2.1 = u) :
    ∀ k, 1 ≤ k → k ≤ m → AvD m 0 2 (P k) k := by
  obtain ⟨p1, p2, p3⟩ := bH_pair huv hP hc
  have hf1 := vfit hP (k := m + 1) (by omega) (by omega)
  rw [fits_h hc.1] at hf1
  have hcol : ∀ x, m ≤ x → x ≤ m + 2 →
      ∀ a < m + 1, ∃ K, m < K ∧ K ≤ 2 * m + 2 ∧ inBar (P K) K a x := by
    intro x hx1 hx2 a ha
    by_cases hai : a = (P (m + 1)).1
    · rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · by_cases hx : x = m
        · exact ⟨m + 1, by omega, by omega, by rw [inBar_h hc.1]; omega⟩
        · exact ⟨m + 2, by omega, by omega, by rw [inBar_h p1]; omega⟩
      · by_cases hx : x = m + 2
        · exact ⟨m + 1, by omega, by omega, by rw [inBar_h hc.1]; omega⟩
        · exact ⟨m + 2, by omega, by omega, by rw [inBar_h p1]; omega⟩
    · obtain ⟨K, h1, h2, h3⟩ := b_rows hP a ha
      have hK : K ≠ m + 2 := by rintro rfl; exact hai (h3.symm.trans p2)
      obtain ⟨d, e1, f⟩ := bH_long hP K (by omega) (by omega)
      exact ⟨K, by omega, by omega, by rw [inBar_h d]; omega⟩
  have A1 := avoid_of_cover hP (by omega) (hcol m le_rfl (by omega))
  have A2 := avoid_of_cover hP (by omega) (hcol (m + 1) (by omega) (by omega))
  have A3 := avoid_of_cover hP (by omega) (hcol (m + 2) (by omega) le_rfl)
  intro k h1 h2
  have hf := vfit hP (k := k) h1 (by omega)
  unfold AvD
  rcases hd : (P k).2.2 with _ | _
  · rw [fits_h hd] at hf
    have B1 := avoid_h hd (A1 k h1 h2)
    have B2 := avoid_h hd (A2 k h1 h2)
    have B3 := avoid_h hd (A3 k h1 h2)
    exact ⟨by omega, fun _ => ⟨by omega, by omega⟩, fun h => by simp at h⟩
  · rw [fits_v hd] at hf
    have B1 := avoid_v hd h1 (A1 k h1 h2)
    have B2 := avoid_v hd h1 (A2 k h1 h2)
    have B3 := avoid_v hd h1 (A3 k h1 h2)
    exact ⟨by omega, fun h => by simp at h, fun _ => ⟨by omega, by omega⟩⟩

/-! ## Class `V`: remove the vertical bar `m + 1` and one of the two middle columns -/

/-- From a big tiling of class `V` to a small tiling. -/
private def PhiV (m e : ℕ) (P : ℕ → Pl) (k : ℕ) : Pl :=
  if k = 0 then dflt else if k ≤ m then mvF m e 1 (P k)
  else if k ≤ 2 * m + 1 then lgF e (P (k + 1)) else dflt

/-- From a small tiling to a big tiling of class `V`. -/
private def PsiV (m e s : ℕ) (Q : ℕ → Pl) (k : ℕ) : Pl :=
  if k = 0 then dflt else if k ≤ m then mvB m e 1 (Q k)
  else if k = m + 1 then (0, s, true)
  else if k ≤ 2 * m + 2 then lgB e (Q (k - 1)) else dflt

/-- `PhiV` maps tilings of class `V` to tilings of the small rectangle. -/
private theorem phiV_valid {m e s : ℕ} (hes : (e = 1 ∧ s = 0) ∨ (e = 0 ∧ s = 2 * m + 2))
    {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P)
    (hc : P (m + 1) = (0, s, true)) :
    Valid (m + 1) (2 * m + 1) (2 * m + 1) (PhiV m e P) := by
  have hlong := bV_long hes hP hc
  have havd := bV_avd hes hP hc
  have hmem : ∀ k, 1 ≤ k → k ≤ 2 * m + 1 → ∀ a b, inBar (PhiV m e P k) k a b ↔
      inBar (P (if k ≤ m then k else k + 1)) (if k ≤ m then k else k + 1) a (cB m e 1 b) := by
    intro k h1 h2 a b
    by_cases hkm : k ≤ m
    · simp only [PhiV, if_neg (show k ≠ 0 by omega), if_pos hkm]
      exact inBar_mvF (havd k h1 hkm)
    · simp only [PhiV, if_neg (show k ≠ 0 by omega), if_neg hkm, if_pos h2]
      obtain ⟨d, e1, f, g, -⟩ := hlong (k + 1) (by omega) (by omega)
      exact inBar_lgF d e1 f (by omega)
  apply valid_of
  · intro k h1 h2
    by_cases hkm : k ≤ m
    · simp only [PhiV, if_neg (show k ≠ 0 by omega), if_pos hkm]
      exact fits_mvF (havd k h1 hkm) (vfit hP h1 (by omega))
    · simp only [PhiV, if_neg (show k ≠ 0 by omega), if_neg hkm, if_pos h2]
      obtain ⟨d, e1, f, g, h⟩ := hlong (k + 1) (by omega) (by omega)
      have hf := vfit hP (k := k + 1) (by omega) (by omega)
      rw [fits_h d] at hf
      rw [fits_h rfl]
      simp only [lgF]
      omega
  · intro a b ha hb
    have hσ : cB m e 1 b < 2 * m + 3 := by unfold cB; split_ifs <;> omega
    obtain ⟨K, hK1, hK2, hin⟩ := vcover hP ha hσ
    by_cases hKm : K ≤ m
    · refine ⟨K, hK1, by omega, (hmem K hK1 (by omega) a b).mpr ?_⟩
      rw [if_pos hKm]; exact hin
    · by_cases hKs : K = m + 1
      · exfalso
        subst hKs
        rw [hc, inBar_v rfl] at hin
        simp only at hin
        unfold cB at hin
        split_ifs at hin <;> omega
      · refine ⟨K - 1, by omega, by omega, (hmem (K - 1) (by omega) (by omega) a b).mpr ?_⟩
        rw [if_neg (by omega), show K - 1 + 1 = K by omega]; exact hin
  · intro a b k1 k2 h1 h2 h3 h4 hin1 hin2
    rw [hmem k1 h1 h2] at hin1
    rw [hmem k2 h3 h4] at hin2
    have := vdisj hP (by split_ifs <;> omega) (by split_ifs <;> omega) (by split_ifs <;> omega)
      (by split_ifs <;> omega) hin1 hin2
    split_ifs at this <;> omega

/-- Membership in the tiles of `PsiV`, read in the small rectangle. -/
private theorem psiV_mem {m e s : ℕ} (hm : 1 ≤ m) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q) :
    ∀ K, 1 ≤ K → K ≤ 2 * m + 2 → K ≠ m + 1 → ∀ a b, e ≤ b →
      (inBar (PsiV m e s Q K) K a b ↔ inBar (Q (if K ≤ m then K else K - 1))
        (if K ≤ m then K else K - 1) a (cF m e 1 b)) := by
  have hl := s_long hm hQ
  have havm := s_avm hm hQ
  intro K h1 h2 h3 a b hb
  by_cases hKm : K ≤ m
  · simp only [PsiV, if_neg (show K ≠ 0 by omega), if_pos hKm]
    exact inBar_mvB (havm K h1 hKm) hb
  · simp only [PsiV, if_neg (show K ≠ 0 by omega), if_neg hKm, if_neg h3, if_pos h2]
    obtain ⟨d, e1, f⟩ := hl (K - 1) (by omega) (by omega)
    have := inBar_lgB (m := m) (e := e) (δ := 1) (k := K - 1) (a := a) d e1 f hb
    rw [show K - 1 + 1 = K by omega] at this
    exact this

/-- The tiles of `PsiV` other than `m + 1` avoid the extra columns and column `s`. -/
private theorem psiV_col {m e s : ℕ} (hm : 1 ≤ m)
    (hes : (e = 1 ∧ s = 0) ∨ (e = 0 ∧ s = 2 * m + 2)) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q) :
    ∀ K, 1 ≤ K → K ≤ 2 * m + 2 → K ≠ m + 1 → ∀ a b, inBar (PsiV m e s Q K) K a b →
      e ≤ b ∧ b ≠ s := by
  intro K h1 h2 h3 a b hin
  have heb : e ≤ b := by
    by_cases hKm : K ≤ m
    · simp only [PsiV, if_neg (show K ≠ 0 by omega), if_pos hKm] at hin
      have := le_cB m e 1 (Q K).2.1
      rcases hd : (Q K).2.2 with _ | _
      · rw [inBar_h (show (mvB m e 1 (Q K)).2.2 = false from hd)] at hin
        simp only [mvB] at hin
        omega
      · rw [inBar_v (show (mvB m e 1 (Q K)).2.2 = true from hd)] at hin
        simp only [mvB] at hin
        omega
    · simp only [PsiV, if_neg (show K ≠ 0 by omega), if_neg hKm, if_neg h3, if_pos h2] at hin
      rw [inBar_h rfl] at hin
      simp only [lgB] at hin
      omega
  refine ⟨heb, fun hbs => ?_⟩
  rw [psiV_mem hm hQ K h1 h2 h3 a b heb] at hin
  have hlt := inBar_lt (vfit hQ (by split_ifs <;> omega) (by split_ifs <;> omega)) hin
  rcases hes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · omega
  · subst hbs
    unfold cF at hlt
    split_ifs at hlt <;> omega

/-- `PsiV` maps tilings of the small rectangle to tilings of the big one. -/
private theorem psiV_valid {m e s : ℕ} (hm : 1 ≤ m)
    (hes : (e = 1 ∧ s = 0) ∨ (e = 0 ∧ s = 2 * m + 2)) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q) :
    Valid (m + 1) (2 * m + 3) (2 * m + 2) (PsiV m e s Q) := by
  have hl := s_long hm hQ
  have havm := s_avm hm hQ
  have hmem := psiV_mem (e := e) (s := s) hm hQ
  have hcol := psiV_col hm hes hQ
  have hsp : ∀ a b, inBar (PsiV m e s Q (m + 1)) (m + 1) a b ↔ b = s ∧ a < m + 1 := by
    intro a b
    simp only [PsiV, if_neg (show m + 1 ≠ 0 by omega), if_neg (show ¬ m + 1 ≤ m by omega),
      if_true]
    rw [inBar_v rfl]
    simp only
    omega
  apply valid_of
  · intro K h1 h2
    by_cases hKm : K ≤ m
    · simp only [PsiV, if_neg (show K ≠ 0 by omega), if_pos hKm]
      exact fits_mvB (by omega) (havm K h1 hKm) (vfit hQ h1 (by omega))
    · by_cases hKs : K = m + 1
      · subst hKs
        simp only [PsiV, if_neg (show m + 1 ≠ 0 by omega), if_neg (show ¬ m + 1 ≤ m by omega),
          if_true]
        rw [fits_v rfl]
        simp only
        omega
      · simp only [PsiV, if_neg (show K ≠ 0 by omega), if_neg hKm, if_neg hKs, if_pos h2]
        obtain ⟨d, e1, f⟩ := hl (K - 1) (by omega) (by omega)
        have hf := vfit hQ (k := K - 1) (by omega) (by omega)
        rw [fits_h d] at hf
        rw [fits_h rfl]
        simp only [lgB]
        omega
  · intro a b ha hb
    by_cases hbs : b = s
    · exact ⟨m + 1, by omega, by omega, (hsp a b).mpr ⟨hbs, ha⟩⟩
    · have heb : e ≤ b := by omega
      have hcf : cF m e 1 b < 2 * m + 1 := by unfold cF; split_ifs <;> omega
      obtain ⟨k, hk1, hk2, hin⟩ := vcover hQ ha hcf
      by_cases hkm : k ≤ m
      · refine ⟨k, hk1, by omega, (hmem k hk1 (by omega) (by omega) a b heb).mpr ?_⟩
        rw [if_pos hkm]; exact hin
      · refine ⟨k + 1, by omega, by omega,
          (hmem (k + 1) (by omega) (by omega) (by omega) a b heb).mpr ?_⟩
        rw [if_neg (by omega), show k + 1 - 1 = k by omega]; exact hin
  · intro a b K1 K2 h1 h2 h3 h4 hin1 hin2
    by_cases hK1 : K1 = m + 1
    · by_cases hK2 : K2 = m + 1
      · omega
      · exfalso
        have := hcol K2 h3 h4 hK2 a b hin2
        subst hK1
        have := (hsp a b).mp hin1
        omega
    · by_cases hK2 : K2 = m + 1
      · exfalso
        have := hcol K1 h1 h2 hK1 a b hin1
        subst hK2
        have := (hsp a b).mp hin2
        omega
      · have c1 := hcol K1 h1 h2 hK1 a b hin1
        have c2 := hcol K2 h3 h4 hK2 a b hin2
        rw [hmem K1 h1 h2 hK1 a b c1.1] at hin1
        rw [hmem K2 h3 h4 hK2 a b c2.1] at hin2
        have := vdisj hQ (by split_ifs <;> omega) (by split_ifs <;> omega)
          (by split_ifs <;> omega) (by split_ifs <;> omega) hin1 hin2
        split_ifs at this <;> omega

/-- `PsiV` undoes `PhiV` on tilings of class `V`. -/
private theorem psiV_phiV {m e s : ℕ} (hes : (e = 1 ∧ s = 0) ∨ (e = 0 ∧ s = 2 * m + 2))
    {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P)
    (hn : ∀ k, (k = 0 ∨ 2 * m + 2 < k) → P k = dflt) (hc : P (m + 1) = (0, s, true)) :
    PsiV m e s (PhiV m e P) = P := by
  have hlong := bV_long hes hP hc
  have havd := bV_avd hes hP hc
  funext k
  by_cases hk0 : k = 0
  · subst hk0; simp only [PsiV, if_true]; exact (hn 0 (Or.inl rfl)).symm
  by_cases hkm : k ≤ m
  · simp only [PsiV, PhiV, if_neg hk0, if_pos hkm]
    exact mvB_mvF (havd k (by omega) hkm)
  by_cases hks : k = m + 1
  · subst hks; simp only [PsiV, if_neg hk0, if_neg hkm, if_true]; exact hc.symm
  by_cases hk2 : k ≤ 2 * m + 2
  · simp only [PsiV, if_neg hk0, if_neg hkm, if_neg hks, if_pos hk2]
    simp only [PhiV, if_neg (show k - 1 ≠ 0 by omega), if_neg (show ¬ k - 1 ≤ m by omega),
      if_pos (show k - 1 ≤ 2 * m + 1 by omega), show k - 1 + 1 = k by omega]
    obtain ⟨d, e1, -⟩ := hlong k (by omega) hk2
    exact lgB_lgF d e1
  · simp only [PsiV, if_neg hk0, if_neg hkm, if_neg hks, if_neg hk2]
    exact (hn k (Or.inr (by omega))).symm

/-- `PhiV` undoes `PsiV`. -/
private theorem phiV_psiV {m e s : ℕ} (hm : 1 ≤ m) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q)
    (hn : ∀ k, (k = 0 ∨ 2 * m + 1 < k) → Q k = dflt) : PhiV m e (PsiV m e s Q) = Q := by
  have hl := s_long hm hQ
  funext k
  by_cases hk0 : k = 0
  · subst hk0; simp only [PhiV, if_true]; exact (hn 0 (Or.inl rfl)).symm
  by_cases hkm : k ≤ m
  · simp only [PhiV, PsiV, if_neg hk0, if_pos hkm]; exact mvF_mvB m e 1 (Q k)
  by_cases hk2 : k ≤ 2 * m + 1
  · simp only [PhiV, if_neg hk0, if_neg hkm, if_pos hk2]
    simp only [PsiV, if_neg (show k + 1 ≠ 0 by omega), if_neg (show ¬ k + 1 ≤ m by omega),
      if_neg (show k + 1 ≠ m + 1 by omega), if_pos (show k + 1 ≤ 2 * m + 2 by omega),
      Nat.add_sub_cancel]
    exact lgF_lgB (hl k (by omega) hk2).1
  · simp only [PhiV, if_neg hk0, if_neg hkm, if_neg hk2]
    exact (hn k (Or.inr (by omega))).symm

open Classical in
/-- Class `V` (with tile `m + 1` in a given end column) has as many tilings as the small
rectangle. -/
private theorem card_classV {m e s : ℕ} (hm : 1 ≤ m)
    (hes : (e = 1 ∧ s = 0) ∨ (e = 0 ∧ s = 2 * m + 2)) :
    ((Univ (m + 1) (2 * m + 3) (2 * m + 2)).filter
      (fun P => Valid (m + 1) (2 * m + 3) (2 * m + 2) P ∧ P (m + 1) = (0, s, true))).card =
    ((Univ (m + 1) (2 * m + 1) (2 * m + 1)).filter
      (Valid (m + 1) (2 * m + 1) (2 * m + 1))).card := by
  apply card_nbij' (PhiV m e) (PsiV m e s)
  · intro P hP
    rw [mem_coe, mem_filter] at hP ⊢
    obtain ⟨hU, hV, hc⟩ := hP
    have hV' := phiV_valid hes hV hc
    refine ⟨mem_Univ_of hV' (fun k hk => ?_), hV'⟩
    simp only [PhiV]
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro Q hQ
    rw [mem_coe, mem_filter] at hQ ⊢
    obtain ⟨hU, hV⟩ := hQ
    have hV' := psiV_valid hm hes hV
    refine ⟨mem_Univ_of hV' (fun k hk => ?_), hV', ?_⟩
    · simp only [PsiV]
      split_ifs <;> first | rfl | (exfalso; omega)
    · simp only [PsiV, if_neg (show m + 1 ≠ 0 by omega), if_neg (show ¬ m + 1 ≤ m by omega),
        if_true]
  · intro P hP
    rw [mem_coe, mem_filter] at hP
    obtain ⟨hU, hV, hc⟩ := hP
    exact psiV_phiV hes hV (mem_Univ.mp hU).1 hc
  · intro Q hQ
    rw [mem_coe, mem_filter] at hQ
    obtain ⟨hU, hV⟩ := hQ
    exact phiV_psiV hm hV (mem_Univ.mp hU).1

/-! ## Class `H`: merge the bars `m + 1`, `m + 2` into one row and remove two middle columns -/

/-- From a big tiling of class `H` to a small tiling. -/
private def PhiH (m : ℕ) (P : ℕ → Pl) (k : ℕ) : Pl :=
  if k = 0 then dflt else if k ≤ m then mvF m 0 2 (P k)
  else if k ≤ 2 * m then lgF 0 (P (k + 2))
  else if k = 2 * m + 1 then ((P (m + 1)).1, 0, false) else dflt

/-- From a small tiling to a big tiling of class `H`. -/
private def PsiH (m u v : ℕ) (Q : ℕ → Pl) (k : ℕ) : Pl :=
  if k = 0 then dflt else if k ≤ m then mvB m 0 2 (Q k)
  else if k = m + 1 then ((Q (2 * m + 1)).1, u, false)
  else if k = m + 2 then ((Q (2 * m + 1)).1, v, false)
  else if k ≤ 2 * m + 2 then lgB 0 (Q (k - 2)) else dflt

/-- `PhiH` maps tilings of class `H` to tilings of the small rectangle. -/
private theorem phiH_valid {m u v : ℕ} (huv : (u = 0 ∧ v = m + 1) ∨ (u = m + 2 ∧ v = 0))
    {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P)
    (hc : (P (m + 1)).2.2 = false ∧ (P (m + 1)).2.1 = u) :
    Valid (m + 1) (2 * m + 1) (2 * m + 1) (PhiH m P) := by
  have hlong := bH_long hP
  have havd := bH_avd huv hP hc
  obtain ⟨p1, p2, p3⟩ := bH_pair huv hP hc
  have hf1 := vfit hP (k := m + 1) (by omega) (by omega)
  rw [fits_h hc.1] at hf1
  have hmem : ∀ k, 1 ≤ k → k ≤ 2 * m → ∀ a b, inBar (PhiH m P k) k a b ↔
      inBar (P (if k ≤ m then k else k + 2)) (if k ≤ m then k else k + 2) a (cB m 0 2 b) := by
    intro k h1 h2 a b
    by_cases hkm : k ≤ m
    · simp only [PhiH, if_neg (show k ≠ 0 by omega), if_pos hkm]
      exact inBar_mvF (havd k h1 hkm)
    · simp only [PhiH, if_neg (show k ≠ 0 by omega), if_neg hkm, if_pos h2]
      obtain ⟨d, e1, f⟩ := hlong (k + 2) (by omega) (by omega)
      exact inBar_lgF d (Nat.zero_le _) (by omega) (by omega)
  have htop : ∀ a b, inBar (PhiH m P (2 * m + 1)) (2 * m + 1) a b ↔
      a = (P (m + 1)).1 ∧ b < 2 * m + 1 := by
    intro a b
    simp only [PhiH, if_neg (show 2 * m + 1 ≠ 0 by omega), if_neg (show ¬ 2 * m + 1 ≤ m by omega),
      if_neg (show ¬ 2 * m + 1 ≤ 2 * m by omega), if_true]
    rw [inBar_h rfl]
    simp only
    omega
  -- the cells of the special row, read in the big rectangle
  have hrow : ∀ a b, b < 2 * m + 1 → a = (P (m + 1)).1 →
      ∃ K, (K = m + 1 ∨ K = m + 2) ∧ inBar (P K) K a (cB m 0 2 b) := by
    intro a b hb ha
    unfold cB
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · by_cases hbm : b ≤ m
      · exact ⟨m + 1, Or.inl rfl, by rw [inBar_h hc.1, if_pos hbm]; omega⟩
      · exact ⟨m + 2, Or.inr rfl, by rw [inBar_h p1, if_neg hbm]; omega⟩
    · by_cases hbm : b ≤ m
      · exact ⟨m + 2, Or.inr rfl, by rw [inBar_h p1, if_pos hbm]; omega⟩
      · exact ⟨m + 1, Or.inl rfl, by rw [inBar_h hc.1, if_neg hbm]; omega⟩
  apply valid_of
  · intro k h1 h2
    by_cases hkm : k ≤ m
    · simp only [PhiH, if_neg (show k ≠ 0 by omega), if_pos hkm]
      exact fits_mvF (havd k h1 hkm) (vfit hP h1 (by omega))
    · by_cases hk2 : k ≤ 2 * m
      · simp only [PhiH, if_neg (show k ≠ 0 by omega), if_neg hkm, if_pos hk2]
        obtain ⟨d, e1, f⟩ := hlong (k + 2) (by omega) (by omega)
        have hf := vfit hP (k := k + 2) (by omega) (by omega)
        rw [fits_h d] at hf
        rw [fits_h rfl]
        simp only [lgF]
        omega
      · have hk : k = 2 * m + 1 := by omega
        subst hk
        simp only [PhiH, if_neg (show 2 * m + 1 ≠ 0 by omega), if_neg hkm, if_neg hk2, if_true]
        rw [fits_h rfl]
        simp only
        omega
  · intro a b ha hb
    have hσ : cB m 0 2 b < 2 * m + 3 := by unfold cB; split_ifs <;> omega
    obtain ⟨K, hK1, hK2, hin⟩ := vcover hP ha hσ
    by_cases hKm : K ≤ m
    · refine ⟨K, hK1, by omega, (hmem K hK1 (by omega) a b).mpr ?_⟩
      rw [if_pos hKm]; exact hin
    · by_cases hKs : K = m + 1 ∨ K = m + 2
      · refine ⟨2 * m + 1, by omega, le_rfl, (htop a b).mpr ⟨?_, hb⟩⟩
        rcases hKs with rfl | rfl
        · rw [inBar_h hc.1] at hin; exact hin.1
        · rw [inBar_h p1] at hin; rw [hin.1, p2]
      · refine ⟨K - 2, by omega, by omega, (hmem (K - 2) (by omega) (by omega) a b).mpr ?_⟩
        rw [if_neg (by omega), show K - 2 + 2 = K by omega]; exact hin
  · intro a b k1 k2 h1 h2 h3 h4 hin1 hin2
    have key : ∀ k, 1 ≤ k → k ≤ 2 * m → inBar (PhiH m P k) k a b →
        inBar (PhiH m P (2 * m + 1)) (2 * m + 1) a b → False := by
      intro k hk1 hk2 hk hs
      rw [hmem k hk1 hk2] at hk
      obtain ⟨ha, hb⟩ := (htop a b).mp hs
      obtain ⟨K, hK, hKin⟩ := hrow a b hb ha
      have := vdisj hP (by split_ifs <;> omega) (by split_ifs <;> omega)
        (show 1 ≤ K by omega) (show K ≤ 2 * m + 2 by omega) hk hKin
      split_ifs at this <;> omega
    by_cases e1 : k1 = 2 * m + 1
    · by_cases e2 : k2 = 2 * m + 1
      · omega
      · subst e1; exact (key k2 h3 (by omega) hin2 hin1).elim
    · by_cases e2 : k2 = 2 * m + 1
      · subst e2; exact (key k1 h1 (by omega) hin1 hin2).elim
      · rw [hmem k1 h1 (by omega)] at hin1
        rw [hmem k2 h3 (by omega)] at hin2
        have := vdisj hP (by split_ifs <;> omega) (by split_ifs <;> omega)
          (by split_ifs <;> omega) (by split_ifs <;> omega) hin1 hin2
        split_ifs at this <;> omega

/-- Membership in the tiles of `PsiH` other than `m + 1`, `m + 2`, read in the small rectangle. -/
private theorem psiH_mem {m u v : ℕ} (hm : 1 ≤ m) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q) :
    ∀ K, 1 ≤ K → K ≤ 2 * m + 2 → K ≠ m + 1 → K ≠ m + 2 → ∀ a b,
      (inBar (PsiH m u v Q K) K a b ↔ inBar (Q (if K ≤ m then K else K - 2))
        (if K ≤ m then K else K - 2) a (cF m 0 2 b)) := by
  have hl := s_long hm hQ
  have havm := s_avm hm hQ
  intro K h1 h2 h3 h4 a b
  by_cases hKm : K ≤ m
  · simp only [PsiH, if_neg (show K ≠ 0 by omega), if_pos hKm]
    exact inBar_mvB (havm K h1 hKm) (Nat.zero_le _)
  · simp only [PsiH, if_neg (show K ≠ 0 by omega), if_neg hKm, if_neg h3, if_neg h4, if_pos h2]
    obtain ⟨d, e1, f⟩ := hl (K - 2) (by omega) (by omega)
    have := inBar_lgB (m := m) (e := 0) (δ := 2) (k := K - 2) (a := a) d e1 f (Nat.zero_le b)
    rw [show K - 2 + 2 = K by omega] at this
    exact this

/-- `PsiH` maps tilings of the small rectangle to tilings of the big one. -/
private theorem psiH_valid {m u v : ℕ} (hm : 1 ≤ m)
    (huv : (u = 0 ∧ v = m + 1) ∨ (u = m + 2 ∧ v = 0)) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q) :
    Valid (m + 1) (2 * m + 3) (2 * m + 2) (PsiH m u v Q) := by
  have hl := s_long hm hQ
  have havm := s_avm hm hQ
  obtain ⟨t1, t2⟩ := s_top hm hQ
  have ht := vfit hQ (k := 2 * m + 1) (by omega) le_rfl
  rw [fits_h t1] at ht
  have hmem := psiH_mem (u := u) (v := v) hm hQ
  have hs1 : ∀ a b, inBar (PsiH m u v Q (m + 1)) (m + 1) a b ↔
      a = (Q (2 * m + 1)).1 ∧ u ≤ b ∧ b < u + (m + 1) := by
    intro a b
    simp only [PsiH, if_neg (show m + 1 ≠ 0 by omega), if_neg (show ¬ m + 1 ≤ m by omega),
      if_true]
    rw [inBar_h rfl]
  have hs2 : ∀ a b, inBar (PsiH m u v Q (m + 2)) (m + 2) a b ↔
      a = (Q (2 * m + 1)).1 ∧ v ≤ b ∧ b < v + (m + 2) := by
    intro a b
    simp only [PsiH, if_neg (show m + 2 ≠ 0 by omega), if_neg (show ¬ m + 2 ≤ m by omega),
      if_neg (show m + 2 ≠ m + 1 by omega), if_true]
    rw [inBar_h rfl]
  -- small tiles other than the full row avoid its row
  have hrow : ∀ k, 1 ≤ k → k ≤ 2 * m → ∀ b, ¬ inBar (Q k) k (Q (2 * m + 1)).1 b := by
    intro k h1 h2 b hin
    have hlt := inBar_lt (vfit hQ h1 (by omega)) hin
    have := vdisj hQ h1 (by omega) (show 1 ≤ 2 * m + 1 by omega) le_rfl hin
      (by rw [inBar_h t1]; omega)
    omega
  apply valid_of
  · intro K h1 h2
    by_cases hKm : K ≤ m
    · simp only [PsiH, if_neg (show K ≠ 0 by omega), if_pos hKm]
      exact fits_mvB (by omega) (havm K h1 hKm) (vfit hQ h1 (by omega))
    · by_cases hK1 : K = m + 1
      · subst hK1
        simp only [PsiH, if_neg (show m + 1 ≠ 0 by omega), if_neg hKm, if_true]
        rw [fits_h rfl]
        simp only
        omega
      · by_cases hK2 : K = m + 2
        · subst hK2
          simp only [PsiH, if_neg (show m + 2 ≠ 0 by omega), if_neg hKm, if_neg hK1, if_true]
          rw [fits_h rfl]
          simp only
          omega
        · simp only [PsiH, if_neg (show K ≠ 0 by omega), if_neg hKm, if_neg hK1, if_neg hK2,
            if_pos h2]
          obtain ⟨d, e1, f⟩ := hl (K - 2) (by omega) (by omega)
          have hf := vfit hQ (k := K - 2) (by omega) (by omega)
          rw [fits_h d] at hf
          rw [fits_h rfl]
          simp only [lgB]
          omega
  · intro a b ha hb
    by_cases hai : a = (Q (2 * m + 1)).1
    · rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · by_cases hbm : b ≤ m
        · exact ⟨m + 1, by omega, by omega, (hs1 a b).mpr ⟨hai, by omega, by omega⟩⟩
        · exact ⟨m + 2, by omega, by omega, (hs2 a b).mpr ⟨hai, by omega, by omega⟩⟩
      · by_cases hbm : b ≤ m + 1
        · exact ⟨m + 2, by omega, by omega, (hs2 a b).mpr ⟨hai, by omega, by omega⟩⟩
        · exact ⟨m + 1, by omega, by omega, (hs1 a b).mpr ⟨hai, by omega, by omega⟩⟩
    · have hcf : cF m 0 2 b < 2 * m + 1 := by unfold cF; split_ifs <;> omega
      obtain ⟨k, hk1, hk2, hin⟩ := vcover hQ ha hcf
      have hk2' : k ≤ 2 * m := by
        by_contra hcon
        have hk : k = 2 * m + 1 := by omega
        subst hk
        rw [inBar_h t1] at hin
        exact hai hin.1
      by_cases hkm : k ≤ m
      · refine ⟨k, hk1, by omega, (hmem k hk1 (by omega) (by omega) (by omega) a b).mpr ?_⟩
        rw [if_pos hkm]; exact hin
      · refine ⟨k + 2, by omega, by omega,
          (hmem (k + 2) (by omega) (by omega) (by omega) (by omega) a b).mpr ?_⟩
        rw [if_neg (by omega), show k + 2 - 2 = k by omega]; exact hin
  · intro a b K1 K2 h1 h2 h3 h4 hin1 hin2
    have hspec : ∀ K, (K = m + 1 ∨ K = m + 2) → inBar (PsiH m u v Q K) K a b →
        a = (Q (2 * m + 1)).1 := by
      rintro K (rfl | rfl) hin
      · exact ((hs1 a b).mp hin).1
      · exact ((hs2 a b).mp hin).1
    have hother : ∀ K, 1 ≤ K → K ≤ 2 * m + 2 → K ≠ m + 1 → K ≠ m + 2 →
        inBar (PsiH m u v Q K) K a b → a ≠ (Q (2 * m + 1)).1 := by
      intro K h1 h2 h3 h4 hin ha
      rw [hmem K h1 h2 h3 h4] at hin
      rw [ha] at hin
      exact hrow _ (by split_ifs <;> omega) (by split_ifs <;> omega) _ hin
    by_cases s1 : K1 = m + 1 ∨ K1 = m + 2
    · have ha := hspec K1 s1 hin1
      by_cases s2 : K2 = m + 1 ∨ K2 = m + 2
      · rcases s1 with rfl | rfl <;> rcases s2 with rfl | rfl
        · rfl
        · have := (hs1 a b).mp hin1; have := (hs2 a b).mp hin2; omega
        · have := (hs2 a b).mp hin1; have := (hs1 a b).mp hin2; omega
        · rfl
      · exact absurd ha (hother K2 h3 h4 (by omega) (by omega) hin2)
    · by_cases s2 : K2 = m + 1 ∨ K2 = m + 2
      · exact absurd (hspec K2 s2 hin2) (hother K1 h1 h2 (by omega) (by omega) hin1)
      · rw [hmem K1 h1 h2 (by omega) (by omega)] at hin1
        rw [hmem K2 h3 h4 (by omega) (by omega)] at hin2
        have := vdisj hQ (by split_ifs <;> omega) (by split_ifs <;> omega)
          (by split_ifs <;> omega) (by split_ifs <;> omega) hin1 hin2
        split_ifs at this <;> omega

/-- `PsiH` undoes `PhiH` on tilings of class `H`. -/
private theorem psiH_phiH {m u v : ℕ} (huv : (u = 0 ∧ v = m + 1) ∨ (u = m + 2 ∧ v = 0))
    {P : ℕ → Pl} (hP : Valid (m + 1) (2 * m + 3) (2 * m + 2) P)
    (hn : ∀ k, (k = 0 ∨ 2 * m + 2 < k) → P k = dflt)
    (hc : (P (m + 1)).2.2 = false ∧ (P (m + 1)).2.1 = u) :
    PsiH m u v (PhiH m P) = P := by
  have hlong := bH_long hP
  have havd := bH_avd huv hP hc
  obtain ⟨p1, p2, p3⟩ := bH_pair huv hP hc
  funext k
  by_cases hk0 : k = 0
  · subst hk0; simp only [PsiH, if_true]; exact (hn 0 (Or.inl rfl)).symm
  by_cases hkm : k ≤ m
  · simp only [PsiH, PhiH, if_neg hk0, if_pos hkm]
    exact mvB_mvF (havd k (by omega) hkm)
  by_cases hk1 : k = m + 1
  · subst hk1
    simp only [PsiH, if_neg hk0, if_neg hkm, if_true]
    simp only [PhiH, if_neg (show 2 * m + 1 ≠ 0 by omega),
      if_neg (show ¬ 2 * m + 1 ≤ m by omega), if_neg (show ¬ 2 * m + 1 ≤ 2 * m by omega),
      if_true]
    exact Prod.ext rfl (Prod.ext hc.2.symm hc.1.symm)
  by_cases hk2 : k = m + 2
  · subst hk2
    simp only [PsiH, if_neg hk0, if_neg hkm, if_neg hk1, if_true]
    simp only [PhiH, if_neg (show 2 * m + 1 ≠ 0 by omega),
      if_neg (show ¬ 2 * m + 1 ≤ m by omega), if_neg (show ¬ 2 * m + 1 ≤ 2 * m by omega),
      if_true]
    exact Prod.ext p2.symm (Prod.ext p3.symm p1.symm)
  by_cases hk3 : k ≤ 2 * m + 2
  · simp only [PsiH, if_neg hk0, if_neg hkm, if_neg hk1, if_neg hk2, if_pos hk3]
    simp only [PhiH, if_neg (show k - 2 ≠ 0 by omega), if_neg (show ¬ k - 2 ≤ m by omega),
      if_pos (show k - 2 ≤ 2 * m by omega), show k - 2 + 2 = k by omega]
    obtain ⟨d, -, -⟩ := hlong k (by omega) hk3
    exact lgB_lgF d (Nat.zero_le _)
  · simp only [PsiH, if_neg hk0, if_neg hkm, if_neg hk1, if_neg hk2, if_neg hk3]
    exact (hn k (Or.inr (by omega))).symm

/-- `PhiH` undoes `PsiH`. -/
private theorem phiH_psiH {m u v : ℕ} (hm : 1 ≤ m) {Q : ℕ → Pl}
    (hQ : Valid (m + 1) (2 * m + 1) (2 * m + 1) Q)
    (hn : ∀ k, (k = 0 ∨ 2 * m + 1 < k) → Q k = dflt) : PhiH m (PsiH m u v Q) = Q := by
  have hl := s_long hm hQ
  obtain ⟨t1, t2⟩ := s_top hm hQ
  funext k
  by_cases hk0 : k = 0
  · subst hk0; simp only [PhiH, if_true]; exact (hn 0 (Or.inl rfl)).symm
  by_cases hkm : k ≤ m
  · simp only [PhiH, PsiH, if_neg hk0, if_pos hkm]; exact mvF_mvB m 0 2 (Q k)
  by_cases hk2 : k ≤ 2 * m
  · simp only [PhiH, if_neg hk0, if_neg hkm, if_pos hk2]
    simp only [PsiH, if_neg (show k + 2 ≠ 0 by omega), if_neg (show ¬ k + 2 ≤ m by omega),
      if_neg (show k + 2 ≠ m + 1 by omega), if_neg (show k + 2 ≠ m + 2 by omega),
      if_pos (show k + 2 ≤ 2 * m + 2 by omega), Nat.add_sub_cancel]
    exact lgF_lgB (hl k (by omega) (by omega)).1
  by_cases hk3 : k = 2 * m + 1
  · subst hk3
    simp only [PhiH, if_neg hk0, if_neg hkm, if_neg hk2, if_true]
    simp only [PsiH, if_neg (show m + 1 ≠ 0 by omega), if_neg (show ¬ m + 1 ≤ m by omega),
      if_true]
    exact Prod.ext rfl (Prod.ext t2.symm t1.symm)
  · simp only [PhiH, if_neg hk0, if_neg hkm, if_neg hk2, if_neg hk3]
    exact (hn k (Or.inr (by omega))).symm

open Classical in
/-- Class `H` (with tile `m + 1` at a given end of its row) has as many tilings as the small
rectangle. -/
private theorem card_classH {m u v : ℕ} (hm : 1 ≤ m)
    (huv : (u = 0 ∧ v = m + 1) ∨ (u = m + 2 ∧ v = 0)) :
    ((Univ (m + 1) (2 * m + 3) (2 * m + 2)).filter
      (fun P => Valid (m + 1) (2 * m + 3) (2 * m + 2) P ∧
        ((P (m + 1)).2.2 = false ∧ (P (m + 1)).2.1 = u))).card =
    ((Univ (m + 1) (2 * m + 1) (2 * m + 1)).filter
      (Valid (m + 1) (2 * m + 1) (2 * m + 1))).card := by
  apply card_nbij' (PhiH m) (PsiH m u v)
  · intro P hP
    rw [mem_coe, mem_filter] at hP ⊢
    obtain ⟨hU, hV, hc⟩ := hP
    have hV' := phiH_valid huv hV hc
    refine ⟨mem_Univ_of hV' (fun k hk => ?_), hV'⟩
    simp only [PhiH]
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro Q hQ
    rw [mem_coe, mem_filter] at hQ ⊢
    obtain ⟨hU, hV⟩ := hQ
    have hV' := psiH_valid hm huv hV
    refine ⟨mem_Univ_of hV' (fun k hk => ?_), hV', ?_⟩
    · simp only [PsiH]
      split_ifs <;> first | rfl | (exfalso; omega)
    · simp only [PsiH, if_neg (show m + 1 ≠ 0 by omega), if_neg (show ¬ m + 1 ≤ m by omega),
        if_true]
      exact ⟨trivial, trivial⟩
  · intro P hP
    rw [mem_coe, mem_filter] at hP
    obtain ⟨hU, hV, hc⟩ := hP
    exact psiH_phiH huv hV (mem_Univ.mp hU).1 hc
  · intro Q hQ
    rw [mem_coe, mem_filter] at hQ
    obtain ⟨hU, hV⟩ := hQ
    exact phiH_psiH hm hV (mem_Univ.mp hU).1

/-! ## Counting: the big rectangle has four times as many tilings -/

open Classical in
/-- **The big rectangle has four times as many tilings**: they split into four classes (tile
`m + 1` is the first or the last column, or lies at the left or the right end of its row), each
in bijection with the tilings of the small rectangle. -/
private theorem card_big {m : ℕ} (hm : 1 ≤ m) :
    ((Univ (m + 1) (2 * m + 3) (2 * m + 2)).filter
      (Valid (m + 1) (2 * m + 3) (2 * m + 2))).card =
    4 * ((Univ (m + 1) (2 * m + 1) (2 * m + 1)).filter
      (Valid (m + 1) (2 * m + 1) (2 * m + 1))).card := by
  have c1 := card_classV hm (e := 1) (s := 0) (Or.inl ⟨rfl, rfl⟩)
  have c2 := card_classV hm (e := 0) (s := 2 * m + 2) (Or.inr ⟨rfl, rfl⟩)
  have c3 := card_classH hm (u := 0) (v := m + 1) (Or.inl ⟨rfl, rfl⟩)
  have c4 := card_classH hm (u := m + 2) (v := 0) (Or.inr ⟨rfl, rfl⟩)
  rw [show ∀ x : ℕ, 4 * x = x + x + x + x from fun x => by ring]
  nth_rw 1 [← c1]
  nth_rw 1 [← c2]
  nth_rw 1 [← c3]
  nth_rw 1 [← c4]
  simp only [card_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro P _
  by_cases hV : Valid (m + 1) (2 * m + 3) (2 * m + 2) P
  · rcases hdd : (P (m + 1)).2.2 with _ | _
    · obtain ⟨-, -, hj⟩ := b_horiz hV hdd
      have n1 : ¬ P (m + 1) = (0, 0, true) := fun h => by rw [h] at hdd; simp at hdd
      have n2 : ¬ P (m + 1) = (0, 2 * m + 2, true) := fun h => by rw [h] at hdd; simp at hdd
      rcases hj with ⟨hj, -⟩ | ⟨hj, -⟩
      · rw [if_pos hV, if_neg (fun h => n1 h.2), if_neg (fun h => n2 h.2),
          if_pos ⟨hV, rfl, hj⟩, if_neg (fun h => by omega)]
      · rw [if_pos hV, if_neg (fun h => n1 h.2), if_neg (fun h => n2 h.2),
          if_neg (fun h => by omega), if_pos ⟨hV, rfl, hj⟩]
    · rcases b_vert hm hV hdd with h | h
      · rw [if_pos hV, if_pos ⟨hV, h⟩, if_neg (fun h' => by rw [h] at h'; simp at h'),
          if_neg (fun h' => absurd h'.2.1 (by simp)), if_neg (fun h' => absurd h'.2.1 (by simp))]
      · rw [if_pos hV, if_neg (fun h' => by rw [h] at h'; simp at h'), if_pos ⟨hV, h⟩,
          if_neg (fun h' => absurd h'.2.1 (by simp)), if_neg (fun h' => absurd h'.2.1 (by simp))]
  · rw [if_neg hV, if_neg (fun h => hV h.1), if_neg (fun h => hV h.1), if_neg (fun h => hV h.1),
      if_neg (fun h => hV h.1)]

/-! ## Counting: the small rectangle has a multiple of four tilings -/

/-- Reflection in the horizontal axis. -/
private def hFlip (m : ℕ) (P : ℕ → Pl) (k : ℕ) : Pl :=
  if k = 0 ∨ 2 * m + 1 < k then dflt
  else if (P k).2.2 = true then (m + 1 - k - (P k).1, (P k).2.1, true)
  else (m - (P k).1, (P k).2.1, false)

/-- Reflection in the vertical axis. -/
private def vFlip (m : ℕ) (P : ℕ → Pl) (k : ℕ) : Pl :=
  if k = 0 ∨ 2 * m + 1 < k then dflt
  else if (P k).2.2 = true then ((P k).1, 2 * m - (P k).2.1, true)
  else ((P k).1, 2 * m + 1 - k - (P k).2.1, false)

/-- Transporting a tiling along a map of the rectangle. -/
private theorem valid_transfer {r c n : ℕ} {P Q : ℕ → Pl} (hP : Valid r c n P)
    (φ : ℕ → ℕ → ℕ × ℕ) (hφ : ∀ a b, a < r → b < c → (φ a b).1 < r ∧ (φ a b).2 < c)
    (hfit : ∀ k, 1 ≤ k → k ≤ n → Fits r c (Q k) k)
    (hmem : ∀ k, 1 ≤ k → k ≤ n → ∀ a b, a < r → b < c →
      (inBar (Q k) k a b ↔ inBar (P k) k (φ a b).1 (φ a b).2)) :
    Valid r c n Q := by
  apply valid_of hfit
  · intro a b ha hb
    obtain ⟨k, h1, h2, hin⟩ := vcover hP (hφ a b ha hb).1 (hφ a b ha hb).2
    exact ⟨k, h1, h2, (hmem k h1 h2 a b ha hb).mpr hin⟩
  · intro a b k1 k2 h1 h2 h3 h4 hin1 hin2
    have hab := inBar_lt (hfit k1 h1 h2) hin1
    exact vdisj hP h1 h2 h3 h4 ((hmem k1 h1 h2 a b hab.1 hab.2).mp hin1)
      ((hmem k2 h3 h4 a b hab.1 hab.2).mp hin2)

/-- The reflection in the horizontal axis maps tilings to tilings. -/
private theorem hFlip_valid {m : ℕ} {P : ℕ → Pl}
    (hP : Valid (m + 1) (2 * m + 1) (2 * m + 1) P) :
    Valid (m + 1) (2 * m + 1) (2 * m + 1) (hFlip m P) := by
  apply valid_transfer hP (fun a b => (m - a, b)) (fun a b ha hb => by simp only; omega)
  · intro k h1 h2
    have hf := vfit hP h1 h2
    simp only [hFlip, if_neg (show ¬ (k = 0 ∨ 2 * m + 1 < k) by omega)]
    rcases hd : (P k).2.2 with _ | _
    · rw [fits_h hd] at hf
      simp only [Bool.false_eq_true, if_false]
      rw [fits_h rfl]; simp only; omega
    · rw [fits_v hd] at hf
      simp only [if_true]
      rw [fits_v rfl]; simp only; omega
  · intro k h1 h2 a b ha hb
    have hf := vfit hP h1 h2
    simp only [hFlip, if_neg (show ¬ (k = 0 ∨ 2 * m + 1 < k) by omega)]
    rcases hd : (P k).2.2 with _ | _
    · rw [fits_h hd] at hf
      simp only [Bool.false_eq_true, if_false]
      rw [inBar_h rfl, inBar_h hd]; simp only; omega
    · rw [fits_v hd] at hf
      simp only [if_true]
      rw [inBar_v rfl, inBar_v hd]; simp only; omega

/-- The reflection in the vertical axis maps tilings to tilings. -/
private theorem vFlip_valid {m : ℕ} {P : ℕ → Pl}
    (hP : Valid (m + 1) (2 * m + 1) (2 * m + 1) P) :
    Valid (m + 1) (2 * m + 1) (2 * m + 1) (vFlip m P) := by
  apply valid_transfer hP (fun a b => (a, 2 * m - b)) (fun a b ha hb => by simp only; omega)
  · intro k h1 h2
    have hf := vfit hP h1 h2
    simp only [vFlip, if_neg (show ¬ (k = 0 ∨ 2 * m + 1 < k) by omega)]
    rcases hd : (P k).2.2 with _ | _
    · rw [fits_h hd] at hf
      simp only [Bool.false_eq_true, if_false]
      rw [fits_h rfl]; simp only; omega
    · rw [fits_v hd] at hf
      simp only [if_true]
      rw [fits_v rfl]; simp only; omega
  · intro k h1 h2 a b ha hb
    have hf := vfit hP h1 h2
    simp only [vFlip, if_neg (show ¬ (k = 0 ∨ 2 * m + 1 < k) by omega)]
    rcases hd : (P k).2.2 with _ | _
    · rw [fits_h hd] at hf
      simp only [Bool.false_eq_true, if_false]
      rw [inBar_h rfl, inBar_h hd]; simp only; omega
    · rw [fits_v hd] at hf
      simp only [if_true]
      rw [inBar_v rfl, inBar_v hd]; simp only; omega

/-- The reflection in the horizontal axis is an involution on tilings. -/
private theorem hFlip_hFlip {m : ℕ} {P : ℕ → Pl}
    (hP : Valid (m + 1) (2 * m + 1) (2 * m + 1) P)
    (hn : ∀ k, (k = 0 ∨ 2 * m + 1 < k) → P k = dflt) : hFlip m (hFlip m P) = P := by
  funext k
  by_cases hk : k = 0 ∨ 2 * m + 1 < k
  · simp only [hFlip, if_pos hk]; exact (hn k hk).symm
  · have hf := vfit hP (k := k) (by omega) (by omega)
    simp only [hFlip, if_neg hk]
    rcases hd : (P k).2.2 with _ | _
    · rw [fits_h hd] at hf
      simp only [Bool.false_eq_true, if_false]
      exact Prod.ext (by simp only; omega) (Prod.ext rfl hd.symm)
    · rw [fits_v hd] at hf
      simp only [if_true]
      exact Prod.ext (by simp only; omega) (Prod.ext rfl hd.symm)

/-- The reflection in the vertical axis is an involution on tilings. -/
private theorem vFlip_vFlip {m : ℕ} {P : ℕ → Pl}
    (hP : Valid (m + 1) (2 * m + 1) (2 * m + 1) P)
    (hn : ∀ k, (k = 0 ∨ 2 * m + 1 < k) → P k = dflt) : vFlip m (vFlip m P) = P := by
  funext k
  by_cases hk : k = 0 ∨ 2 * m + 1 < k
  · simp only [vFlip, if_pos hk]; exact (hn k hk).symm
  · have hf := vfit hP (k := k) (by omega) (by omega)
    simp only [vFlip, if_neg hk]
    rcases hd : (P k).2.2 with _ | _
    · rw [fits_h hd] at hf
      simp only [Bool.false_eq_true, if_false]
      exact Prod.ext rfl (Prod.ext (by simp only; omega) hd.symm)
    · rw [fits_v hd] at hf
      simp only [if_true]
      exact Prod.ext rfl (Prod.ext (by simp only; omega) hd.symm)

/-- Distinguishes a tiling from its reflection in the horizontal axis. -/
private def alpha (m : ℕ) (P : ℕ → Pl) : Prop :=
  2 * (P (2 * m + 1)).1 < m ∨ (2 * (P (2 * m + 1)).1 = m ∧ 2 * (P (2 * m)).1 < m)

/-- Distinguishes a tiling from its reflection in the vertical axis. -/
private def beta (m : ℕ) (P : ℕ → Pl) : Prop := (P (2 * m)).2.1 = 0

/-- How the two reflections act on `alpha` and `beta`. -/
private theorem flip_alpha_beta {m : ℕ} (hm : 1 ≤ m) {P : ℕ → Pl}
    (hP : Valid (m + 1) (2 * m + 1) (2 * m + 1) P) :
    (alpha m (hFlip m P) ↔ ¬ alpha m P) ∧ (beta m (hFlip m P) ↔ beta m P) ∧
      (alpha m (vFlip m P) ↔ alpha m P) ∧ (beta m (vFlip m P) ↔ ¬ beta m P) := by
  obtain ⟨t1, t2⟩ := s_top hm hP
  obtain ⟨u1, u2, u3⟩ := s_two hm hP
  have ht := vfit hP (k := 2 * m + 1) (by omega) le_rfl
  have hu := vfit hP (k := 2 * m) (by omega) (by omega)
  rw [fits_h t1] at ht
  rw [fits_h u1] at hu
  have h1 : hFlip m P (2 * m + 1) = (m - (P (2 * m + 1)).1, (P (2 * m + 1)).2.1, false) := by
    rw [hFlip, if_neg (by omega), if_neg (by rw [t1]; simp)]
  have h2 : hFlip m P (2 * m) = (m - (P (2 * m)).1, (P (2 * m)).2.1, false) := by
    rw [hFlip, if_neg (by omega), if_neg (by rw [u1]; simp)]
  have h3 : vFlip m P (2 * m + 1) =
      ((P (2 * m + 1)).1, 2 * m + 1 - (2 * m + 1) - (P (2 * m + 1)).2.1, false) := by
    rw [vFlip, if_neg (by omega), if_neg (by rw [t1]; simp)]
  have h4 : vFlip m P (2 * m) = ((P (2 * m)).1, 2 * m + 1 - 2 * m - (P (2 * m)).2.1, false) := by
    rw [vFlip, if_neg (by omega), if_neg (by rw [u1]; simp)]
  simp only [alpha, beta, h1, h2, h3, h4, true_and]
  omega

open Classical in
/-- The number of tilings of the small rectangle is divisible by `4`: the reflections pair
up the tilings with and without `alpha`, and then those with and without `beta`. -/
private theorem four_dvd_small {m : ℕ} (hm : 1 ≤ m) :
    4 ∣ ((Univ (m + 1) (2 * m + 1) (2 * m + 1)).filter
      (Valid (m + 1) (2 * m + 1) (2 * m + 1))).card := by
  set S := (Univ (m + 1) (2 * m + 1) (2 * m + 1)).filter
    (Valid (m + 1) (2 * m + 1) (2 * m + 1)) with hS
  have memS : ∀ P, P ∈ S ↔ Valid (m + 1) (2 * m + 1) (2 * m + 1) P ∧
      ∀ k, (k = 0 ∨ 2 * m + 1 < k) → P k = dflt := by
    intro P
    rw [hS, mem_filter]
    constructor
    · rintro ⟨hU, hV⟩; exact ⟨hV, (mem_Univ.mp hU).1⟩
    · rintro ⟨hV, hn⟩; exact ⟨mem_Univ_of hV hn, hV⟩
  have hnh : ∀ P, ∀ k, (k = 0 ∨ 2 * m + 1 < k) → hFlip m P k = dflt := by
    intro P k hk; simp only [hFlip, if_pos hk]
  have hnv : ∀ P, ∀ k, (k = 0 ∨ 2 * m + 1 < k) → vFlip m P k = dflt := by
    intro P k hk; simp only [vFlip, if_pos hk]
  have e1 : (S.filter (alpha m)).card = (S.filter (fun P => ¬ alpha m P)).card := by
    apply card_nbij' (hFlip m) (hFlip m)
    · intro P hP
      rw [mem_coe, mem_filter, memS] at hP ⊢
      exact ⟨⟨hFlip_valid hP.1.1, hnh P⟩, fun h => ((flip_alpha_beta hm hP.1.1).1.mp h) hP.2⟩
    · intro P hP
      rw [mem_coe, mem_filter, memS] at hP ⊢
      exact ⟨⟨hFlip_valid hP.1.1, hnh P⟩, (flip_alpha_beta hm hP.1.1).1.mpr hP.2⟩
    · intro P hP
      rw [mem_coe, mem_filter, memS] at hP
      exact hFlip_hFlip hP.1.1 hP.1.2
    · intro P hP
      rw [mem_coe, mem_filter, memS] at hP
      exact hFlip_hFlip hP.1.1 hP.1.2
  have e2 : ((S.filter (alpha m)).filter (beta m)).card =
      ((S.filter (alpha m)).filter (fun P => ¬ beta m P)).card := by
    apply card_nbij' (vFlip m) (vFlip m)
    · intro P hP
      rw [mem_coe, mem_filter, mem_filter, memS] at hP ⊢
      have hab := flip_alpha_beta hm hP.1.1.1
      exact ⟨⟨⟨vFlip_valid hP.1.1.1, hnv P⟩, hab.2.2.1.mpr hP.1.2⟩, fun h => (hab.2.2.2.mp h) hP.2⟩
    · intro P hP
      rw [mem_coe, mem_filter, mem_filter, memS] at hP ⊢
      have hab := flip_alpha_beta hm hP.1.1.1
      exact ⟨⟨⟨vFlip_valid hP.1.1.1, hnv P⟩, hab.2.2.1.mpr hP.1.2⟩, hab.2.2.2.mpr hP.2⟩
    · intro P hP
      rw [mem_coe, mem_filter, mem_filter, memS] at hP
      exact vFlip_vFlip hP.1.1.1 hP.1.1.2
    · intro P hP
      rw [mem_coe, mem_filter, mem_filter, memS] at hP
      exact vFlip_vFlip hP.1.1.1 hP.1.1.2
  have t1 := card_filter_add_card_filter_not (s := S) (alpha m)
  have t2 := card_filter_add_card_filter_not (s := S.filter (alpha m)) (beta m)
  exact ⟨((S.filter (alpha m)).filter (beta m)).card, by omega⟩

/-! ## The conjecture -/

/-- Unfolding `a`. -/
private theorem a_eq {n r c : ℕ} (hr : rows n = r) (hc : cols n = c) :
    a n = search (c + 1) (r * (c + 1)) n (stabCount r c (c + 1) n) n (rectMask r c (c + 1)) 0 /
      (1 + (otherSymmetries r c).length) := by
  subst hr hc; rfl

/-- `rows (2m + 1) = m + 1`. -/
private theorem rows_odd (m : ℕ) : rows (2 * m + 1) = m + 1 := by
  unfold rows; omega

/-- `cols (2m + 1) = 2m + 1`. -/
private theorem cols_odd (m : ℕ) : cols (2 * m + 1) = 2 * m + 1 := by
  unfold cols
  rw [rows_odd]
  have : (2 * m + 1) * (2 * m + 1 + 1) / 2 = (2 * m + 1) * (m + 1) := by
    rw [show (2 * m + 1) * (2 * m + 1 + 1) = 2 * ((2 * m + 1) * (m + 1)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  rw [this, Nat.mul_div_cancel _ (by omega)]

/-- `rows (2m + 2) = m + 1`. -/
private theorem rows_even (m : ℕ) : rows (2 * m + 2) = m + 1 := by
  unfold rows; omega

/-- `cols (2m + 2) = 2m + 3`. -/
private theorem cols_even (m : ℕ) : cols (2 * m + 2) = 2 * m + 3 := by
  unfold cols
  rw [rows_even]
  have : (2 * m + 2) * (2 * m + 2 + 1) / 2 = (2 * m + 3) * (m + 1) := by
    rw [show (2 * m + 2) * (2 * m + 2 + 1) = 2 * ((2 * m + 3) * (m + 1)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  rw [this, Nat.mul_div_cancel _ (by omega)]

open Classical in
/-- `a (2m + 1)` is the number of tilings of `(m + 1) × (2m + 1)` divided by `4`. -/
private theorem a_odd {m : ℕ} (hm : 1 ≤ m) :
    a (2 * m + 1) = ((Univ (m + 1) (2 * m + 1) (2 * m + 1)).filter
      (Valid (m + 1) (2 * m + 1) (2 * m + 1))).card / 4 := by
  rw [a_eq (rows_odd m) (cols_odd m)]
  exact search_count (by omega) (by omega) (by omega) (by omega)

open Classical in
/-- `a (2m + 2)` is the number of tilings of `(m + 1) × (2m + 3)` divided by `4`. -/
private theorem a_even {m : ℕ} (hm : 1 ≤ m) :
    a (2 * m + 2) = ((Univ (m + 1) (2 * m + 3) (2 * m + 2)).filter
      (Valid (m + 1) (2 * m + 3) (2 * m + 2))).card / 4 := by
  rw [a_eq (rows_even m) (cols_even m)]
  exact search_count (by omega) (by omega) (by omega) (by omega)

/-- **A394981, the conjecture `a(n + 1) = 4 a(n)` for odd `n ≥ 3`.** -/
theorem result : statement := by
  intro n hn hodd
  obtain ⟨m, rfl⟩ := hodd
  have hm : 1 ≤ m := by omega
  rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, a_even hm, a_odd hm, card_big hm]
  obtain ⟨q, hq⟩ := four_dvd_small hm
  rw [hq]
  omega

end Math0.Frontier.A394981

#math0_settles Math0.Frontier.A394981.result Math0.Statements.A394981.statement
