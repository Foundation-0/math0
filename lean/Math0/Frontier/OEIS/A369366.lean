/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A369366
import Math0.Audit

/-!
# The least number of inequivalent cells of a `(6k+5)`-iamond is `3(k+1)`

We prove Exley's conjecture `a(6k+5) = 3(k+1)` for every `k ≥ 0` (OEIS A369366).

**Lower bound.** Let `P` be a set of `n ≡ 5 (mod 6)` cells and `g` a symmetry of the grid with
`g(P) = P`.
* `g` preserves orientation (`neg = false`): a map `x ↦ -σ(x) + t` sends a cell of coordinate sum
  `s` to one of coordinate sum `1 - s`, so summing `sumC` over `P` gives `2·Σ sumC = n`, which is
  impossible for odd `n` (`neg_eq_false`).
* If the permutation `σ` of `g` is even, `g` is the identity. For `σ = id`, `g` is a translation
  and the centroid forces `t = 0` (`t_eq_of_sym`). For `σ` a cyclic shift, `g` is a
  `120°`-rotation: `g³ = id` (`rot3_cube`) and it fixes at most one cell (`rot3_fix`: the
  difference of two fixed cells is `(d, d, d)`, whose sum `3d` lies in `{-1, 0, 1}`), so
  `n ≡ #fixed cells ∈ {0, 1} (mod 3)` (`Equiv.Perm.card_fixedPoints_modEq`), contradicting
  `n ≡ 2 (mod 3)` (`no_rot3`, `rot_trivial`).
* Hence among cells `c, d = g(c), e = h(c)` of one class, either `g` or `h` has an even
  permutation (so `d = c` or `e = c`), or both are odd and `h ∘ g⁻¹` (an even permutation) maps `d`
  to `e`, so `d = e` (`three`). Every class has at most two cells (`card_cls_le`), so
  `n ≤ 2 · numClasses P` (`lower`), i.e. `numClasses P ≥ 3(k+1)`.

**Upper bound.** The straight strip of `n = 2m + 1` triangles, cells
`(⌈j/2⌉, -⌊j/2⌋, 0)` for `j < n` (`strip`), is a polyiamond (`strip_isPolyiamond`) whose mirror
symmetry `(a, b, c) ↦ (b + m, a - m, c)` exchanges cells `j` and `2m - j` (`mirror_app`), so its
classes are among those of the cells `0, …, m`: at most `m + 1 = 3(k+1)` classes (`upper`).
-/

namespace Math0.Frontier.A369366
open Math0.Statements.A369366

/-- `perm 3` is the cyclic shift `(a, b, c) ↦ (b, c, a)`. -/
private theorem perm_three (x : Pt) : perm 3 x = (x.2.1, x.2.2, x.1) := rfl

/-- `perm 4` is the cyclic shift `(a, b, c) ↦ (c, a, b)`. -/
private theorem perm_four (x : Pt) : perm 4 x = (x.2.2, x.1, x.2.1) := rfl

/-- `perm 2` swaps the first two coordinates. -/
private theorem perm_two (x : Pt) : perm 2 x = (x.2.1, x.1, x.2.2) := rfl

/-- A symmetry of a set of cells of odd size preserves the orientation of the cells
(`x ↦ -σ(x) + t` exchanges the cells with coordinate sum `0` and `1`). -/
private theorem neg_eq_false {P : Finset Pt} (hodd : P.card % 2 = 1) {g : Isom}
    (hg : P.image g.app = P) : g.neg = false := by
  by_contra hn
  have hn : g.neg = true := by simpa using hn
  have h1 : ∑ x ∈ P, sumC (g.app x) = ∑ x ∈ P, sumC x := by
    conv_rhs => rw [← hg]
    rw [Finset.sum_image fun x _ y _ h => g.app_injective h]
  have h2 : ∀ x, sumC (g.app x) = 1 - sumC x := by
    intro x
    rw [Isom.app, sumC_add, sumC_lin, g.ht, hn]
    simp [tReq]
    ring
  simp only [h2, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
  omega

/-- A `120°`-rotation `x ↦ σ(x) + t` (`σ` a cyclic shift, `t₁ + t₂ + t₃ = 0`) has order `3`. -/
private theorem rot3_cube {g : Isom} (hn : g.neg = false) (hs : g.s = 3 ∨ g.s = 4) (x : Pt) :
    g.app (g.app (g.app x)) = x := by
  obtain ⟨s, n, ⟨t1, t2, t3⟩, ht⟩ := g
  simp only at hn hs
  subst hn
  obtain ⟨a, b, c⟩ := x
  simp only [sumC, tReq, Bool.false_eq_true, if_false] at ht
  rcases hs with rfl | rfl <;>
  · simp only [Isom.app, lin, perm_three, perm_four, Bool.false_eq_true, if_false,
      Prod.mk_add_mk, Prod.mk.injEq]
    omega

/-- A `120°`-rotation fixes at most one cell. -/
private theorem rot3_fix {g : Isom} (hn : g.neg = false) (hs : g.s = 3 ∨ g.s = 4) {x y : Pt}
    (hx : IsCell x) (hy : IsCell y) (hgx : g.app x = x) (hgy : g.app y = y) : x = y := by
  obtain ⟨s, n, ⟨t1, t2, t3⟩, ht⟩ := g
  simp only at hn hs
  subst hn
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := y
  simp only [IsCell, sumC] at hx hy
  rcases hs with rfl | rfl <;>
  · simp only [Isom.app, lin, perm_three, perm_four, Bool.false_eq_true, if_false,
      Prod.mk_add_mk, Prod.mk.injEq] at hgx hgy ⊢
    omega

/-- No set of cells whose size is `2 mod 3` has a `120°`-rotation symmetry: the rotation permutes
the cells with orbits of size `1` or `3` and fixes at most one cell. -/
private theorem no_rot3 {P : Finset Pt} (hcell : ∀ x ∈ P, IsCell x) (h3 : P.card % 3 = 2)
    {g : Isom} (hg : P.image g.app = P) (hn : g.neg = false) (hs : g.s = 3 ∨ g.s = 4) : False := by
  classical
  have hmem : ∀ x ∈ P, g.app x ∈ P := (image_eq_iff P g).1 hg
  let f : Function.End {x // x ∈ P} := fun x => ⟨g.app x.1, hmem x.1 x.2⟩
  have hpow : f ^ 3 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    exact rot3_cube hn hs x.1
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hpow
  have hfix : Fintype.card (Function.fixedPoints f) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    rintro ⟨⟨x, hx⟩, hxf⟩ ⟨⟨y, hy⟩, hyf⟩
    have hxf' : g.app x = x := congrArg Subtype.val hxf
    have hyf' : g.app y = y := congrArg Subtype.val hyf
    have := rot3_fix hn hs (hcell x hx) (hcell y hy) hxf' hyf'
    subst this
    rfl
  rw [Fintype.card_coe] at hmod
  unfold Nat.ModEq at hmod
  omega

/-- For a set of cells of size `5 mod 6`, every symmetry whose linear part is an even
permutation (a rotation) is the identity. -/
private theorem rot_trivial {P : Finset Pt} (hcell : ∀ x ∈ P, IsCell x) (hcard : P.card % 6 = 5)
    {g : Isom} (hg : P.image g.app = P) (hs : g.s = 0 ∨ g.s = 3 ∨ g.s = 4) (x : Pt) :
    g.app x = x := by
  have hn : g.neg = false := neg_eq_false (by omega) hg
  rcases hs with hs | hs
  · have hne : P.Nonempty := Finset.card_pos.1 (by omega)
    have ht := t_eq_of_sym hne hg
    rw [hs, hn, lin_zero, sub_self] at ht
    have ht0 : g.t = 0 := by
      rw [ht]
      simp [divPt]
    rw [Isom.app, hs, hn, lin_zero, ht0, add_zero]
  · exact (no_rot3 hcell (by omega) hg hn hs).elim

/-- The composition `h ∘ g⁻¹` of two reflections (odd permutations) is a rotation. -/
private theorem mulTab_inv_even (i j : Fin 6) (hi : i = 1 ∨ i = 2 ∨ i = 5)
    (hj : j = 1 ∨ j = 2 ∨ j = 5) :
    mulTab j (invTab i) = 0 ∨ mulTab j (invTab i) = 3 ∨ mulTab j (invTab i) = 4 := by
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> decide

/-- The indices of the even permutations are `0, 3, 4`; those of the odd ones are `1, 2, 5`. -/
private theorem fin6_cases (i : Fin 6) :
    (i = 0 ∨ i = 3 ∨ i = 4) ∨ (i = 1 ∨ i = 2 ∨ i = 5) := by
  fin_cases i <;> simp

/-- Among three cells `c, d, e` of `P` with `d, e` equivalent to `c`, two coincide. -/
private theorem three {P : Finset Pt} (hcell : ∀ x ∈ P, IsCell x) (hcard : P.card % 6 = 5)
    {c d e : Pt} (hd : Equivalent P c d) (he : Equivalent P c e) : d = c ∨ e = c ∨ d = e := by
  obtain ⟨g, hg, rfl⟩ := hd
  obtain ⟨h, hh, rfl⟩ := he
  rcases fin6_cases g.s with hgs | hgs
  · exact Or.inl (rot_trivial hcell hcard hg hgs c)
  rcases fin6_cases h.s with hhs | hhs
  · exact Or.inr (Or.inl (rot_trivial hcell hcard hh hhs c))
  have hk : P.image (h.comp g.inv).app = P := by
    rw [← image_image_app]
    conv_lhs => rw [← hg]
    rw [image_inv_image, hh]
  have := rot_trivial hcell hcard hk (mulTab_inv_even g.s h.s hgs hhs) (g.app c)
  rw [Isom.comp_app, Isom.inv_app_app] at this
  exact Or.inr (Or.inr this.symm)

/-- In a set of cells of size `5 mod 6`, every class of equivalent cells has at most two cells. -/
private theorem card_cls_le {P : Finset Pt} (hcell : ∀ x ∈ P, IsCell x) (hcard : P.card % 6 = 5)
    (c : Pt) : (cls P c).card ≤ 2 := by
  by_contra hlt
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.1 (show 2 < (cls P c).card by omega)
  simp only [cls, Finset.mem_filter] at hx hy hz
  have hxy' := equivalent_trans (equivalent_symm hx.2) hy.2
  have hxz' := equivalent_trans (equivalent_symm hx.2) hz.2
  rcases three hcell hcard hxy' hxz' with h | h | h
  · exact hxy h.symm
  · exact hxz h.symm
  · exact hyz h

/-- Lower bound: a set of `n ≡ 5 (mod 6)` cells has at least `(n + 1) / 2` classes. -/
private theorem lower {P : Finset Pt} (hcell : ∀ x ∈ P, IsCell x) (hcard : P.card % 6 = 5) :
    P.card ≤ 2 * numClasses P := by
  unfold numClasses
  apply Finset.card_le_mul_card_image
  intro b hb
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hb
  calc (P.filter fun a => cls P a = cls P c).card ≤ (cls P c).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [← hx.2]
        simp only [cls, Finset.mem_filter]
        exact ⟨hx.1, equivalent_refl P x⟩
    _ ≤ 2 := card_cls_le hcell hcard c

/-! ### The straight strip -/

/-- The `j`-th cell `(⌈j/2⌉, -⌊j/2⌋, 0)` of the straight strip (a row of triangles). -/
private def stripCell (j : ℕ) : Pt := ((((j + 1) / 2 : ℕ) : ℤ), -(((j / 2 : ℕ)) : ℤ), 0)

/-- The straight strip of `n` triangles. -/
private def strip (n : ℕ) : Finset Pt := (Finset.range n).image stripCell

/-- Distinct indices give distinct cells of the strip (`j = a - b`). -/
private theorem stripCell_injective : Function.Injective stripCell := by
  intro i j h
  simp only [stripCell, Prod.mk.injEq] at h
  omega

/-- Every cell of the strip is a cell of the grid (coordinate sum `⌈j/2⌉ - ⌊j/2⌋ ∈ {0, 1}`). -/
private theorem stripCell_isCell (j : ℕ) : IsCell (stripCell j) := by
  simp only [IsCell, sumC, stripCell]
  omega

/-- Consecutive cells of the strip share an edge. -/
private theorem stripCell_adj (j : ℕ) : Adj (stripCell j) (stripCell (j + 1)) := by
  unfold Adj stripCell
  simp only
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have e1 : (((j + 1 + 1) / 2 : ℕ) : ℤ) - (((j + 1) / 2 : ℕ) : ℤ) = 1 := by omega
    have e2 : -((((j + 1) / 2 : ℕ)) : ℤ) - -(((j / 2 : ℕ)) : ℤ) = 0 := by omega
    rw [e1, e2]
    norm_num
  · have e1 : (((j + 1 + 1) / 2 : ℕ) : ℤ) - (((j + 1) / 2 : ℕ) : ℤ) = 0 := by omega
    have e2 : -((((j + 1) / 2 : ℕ)) : ℤ) - -(((j / 2 : ℕ)) : ℤ) = -1 := by omega
    rw [e1, e2]
    norm_num

/-- The `j`-th cell belongs to the strip of `n > j` triangles. -/
private theorem stripCell_mem {n j : ℕ} (hj : j < n) : stripCell j ∈ strip n :=
  Finset.mem_image_of_mem _ (Finset.mem_range.2 hj)

/-- Chains in `P` can be reversed. -/
private theorem rtg_symm {P : Finset Pt} {x y : Pt} (h : Relation.ReflTransGen (Step P) x y) :
    Relation.ReflTransGen (Step P) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, adj_symm hbc.2.2⟩ ih

/-- The strip is a polyiamond. -/
private theorem strip_isPolyiamond (n : ℕ) : IsPolyiamond n (strip n) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [strip, Finset.card_image_of_injective _ stripCell_injective, Finset.card_range]
  · intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
    exact stripCell_isCell j
  · have up : ∀ i d, i + d < n →
        Relation.ReflTransGen (Step (strip n)) (stripCell i) (stripCell (i + d)) := by
      intro i d
      induction d with
      | zero => intro _; exact Relation.ReflTransGen.refl
      | succ d ih =>
        intro hd
        exact (ih (by omega)).tail
          ⟨stripCell_mem (by omega), stripCell_mem (by omega), stripCell_adj (i + d)⟩
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    rw [Finset.mem_range] at hi hj
    rcases le_total i j with hij | hij
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      exact up i d hj
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      exact rtg_symm (up j d hi)

/-- The mirror symmetry `(a, b, c) ↦ (b + m, a - m, c)` of the strip of `2m + 1` triangles. -/
private def mirror (m : ℕ) : Isom := ⟨2, false, ((m : ℤ), -(m : ℤ), 0), by simp [sumC, tReq]⟩

/-- The mirror symmetry exchanges the cells `j` and `2m - j` of the strip. -/
private theorem mirror_app (m j : ℕ) (hj : j ≤ 2 * m) :
    (mirror m).app (stripCell j) = stripCell (2 * m - j) := by
  simp only [mirror, Isom.app, lin, perm_two, stripCell, Bool.false_eq_true, if_false,
    Prod.mk_add_mk, Prod.mk.injEq]
  omega

/-- The cells `j` and `2m - j` of the strip of `2m + 1` triangles are equivalent. -/
private theorem equivalent_mirror (m j : ℕ) (hj : j ≤ 2 * m) :
    Equivalent (strip (2 * m + 1)) (stripCell j) (stripCell (2 * m - j)) := by
  refine ⟨mirror m, (image_eq_iff _ _).2 fun x hx => ?_, mirror_app m j hj⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  rw [Finset.mem_range] at hi
  rw [mirror_app m i (by omega)]
  exact stripCell_mem (by omega)

/-- Equivalent cells have the same class. -/
private theorem cls_eq {P : Finset Pt} {c d : Pt} (h : Equivalent P c d) : cls P c = cls P d := by
  ext y
  simp only [cls, Finset.mem_filter]
  exact and_congr_right fun _ =>
    ⟨fun h' => equivalent_trans (equivalent_symm h) h', fun h' => equivalent_trans h h'⟩

/-- Upper bound: the strip of `2m + 1` triangles has at most `m + 1` classes. -/
private theorem upper (m : ℕ) : numClasses (strip (2 * m + 1)) ≤ m + 1 := by
  unfold numClasses
  have hsub : (strip (2 * m + 1)).image (cls (strip (2 * m + 1))) ⊆
      (Finset.range (m + 1)).image fun j => cls (strip (2 * m + 1)) (stripCell j) := by
    intro C hC
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hC
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_range] at hj
    rcases le_or_gt j m with hjm | hjm
    · exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))
    · refine Finset.mem_image.2 ⟨2 * m - j, Finset.mem_range.2 (by omega), ?_⟩
      rw [cls_eq (equivalent_mirror m j (by omega))]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.range (m + 1)).card := Finset.card_image_le
    _ = m + 1 := Finset.card_range _

/-- Exley's conjecture: `a(6k + 5) = 3(k + 1)` for every `k ≥ 0`. -/
theorem result : statement := by
  intro k
  have hP := strip_isPolyiamond (6 * k + 5)
  have hub : numClasses (strip (6 * k + 5)) ≤ 3 * (k + 1) := by
    have := upper (3 * k + 2)
    rwa [show 2 * (3 * k + 2) + 1 = 6 * k + 5 by ring] at this
  unfold a
  apply le_antisymm
  · exact le_trans (Nat.sInf_le ⟨_, hP, rfl⟩) hub
  · refine le_csInf ⟨_, strip (6 * k + 5), hP, rfl⟩ ?_
    rintro m ⟨P, ⟨hcard, hcell, -⟩, rfl⟩
    have := lower hcell (by omega)
    omega

end Math0.Frontier.A369366

#math0_settles Math0.Frontier.A369366.result Math0.Statements.A369366.statement
