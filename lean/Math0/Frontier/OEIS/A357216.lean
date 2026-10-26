/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A357216
import Math0.Audit

/-!
# Internal `n`-gons in a regular `n`-gon: Shannon's conjecture (OEIS A357216)

We prove both parts of `statement`: for `n ≥ 3` some `k` gives a point on three of the drawn
sides iff `n ∈ {3, 4, 6}`, and for `n = 5` and every `n ≥ 7` the `k` internal `n`-gons cut the
regular `n`-gon into exactly `n k² + 1` regions.

**Frames.** At the corner `V_C` of the polygon write `z = V_C + x (V_{C-1} - V_C) + y (V_{C+1} - V_C)`
(`fx`, `fy`; real-affine in `z`). The vertex `V_{C+a}` has frame coordinates
`X(a) = sin(aφ) sin((a-1)φ) / (sin φ sin 2φ)`, `Y(a) = sin(aφ) sin((a+1)φ) / (sin φ sin 2φ)`
with `φ = π/n` (`Xr`, `Yr`). In particular `V_{C±1}, V_{C±2}` are `(1,0), (0,1), (1+u,1), (1,1+u)`
with `W = 1 + u = 1 + 2 cos(2π/n)`, and every vertex other than `V_C` has `x, y ≥ 0`, `x + y ≥ 1`.
So the polygon lies in each corner angle, and the open corner triangle lies in its interior.

**Chords and lines.** The side `(j, m)` of the internal polygon number `m+1` is the chord at the
corner `V_{j+1}` from `(1-t, 0)` to `(0, t)`, `t = (m+1)/(k+1)`, on the line
`Fl = t x + (1-t) y - t(1-t) = 0`. The line meets the open polygon exactly in the open chord.
Along chord `(j, m)` (parameter `r`) the line of chord `(j', m')` (parameter `s`) is the affine
function `(1-r) a + r b`, computed from the frame values: same corner: `(t - s)(r - s)`; next
corner: a root in `(0,1)` iff `s < t`; previous corner: iff `s > t`; other corners: none.

**No triple points (`n = 5`, `n ≥ 7`).** Three concurrent lines would give two at one corner and
one at an adjacent corner, and then an equation `α W + β = 0` with rational `α ≠ 0`, `β`. But `W`
is irrational by Niven's theorem (`niven`).

**Counting.** A general theorem (`count_general`): if lines `f_i = 0`, added in order, each meet an
open convex set `U` in an open segment, then the components of `U` minus the lines are the
realised sign vectors, and their number is `1 + ∑_i (1 + #distinct points of segment i on earlier
lines)`. Adding the chords in order of `m`, the chord `(j, m)` meets `2m` earlier lines in distinct
points (the `m` earlier chords at its corner and the `m` at the next corner), so the count is
`1 + ∑_{m<k} n (1 + 2m) = n k² + 1`.

**Non-simple intersections for `n = 3, 4, 6`.** Explicit triple points at `k = 5, 5, 9`.
-/

namespace Math0.Frontier.A357216
open Math0.Statements.A357216
open Set Topology

/-- The points of `U` off the first `N` lines. -/
private def cellSet (U : Set ℂ) (f : ℕ → ℂ → ℝ) (N : ℕ) : Set ℂ := {z | z ∈ U ∧ ∀ i < N, f i z ≠ 0}

/-- Sign vector of `z` with respect to the first `N` lines. -/
private noncomputable def sgn (f : ℕ → ℂ → ℝ) (N : ℕ) (z : ℂ) : Finset ℕ :=
  (Finset.range N).filter (fun i => 0 < f i z)

/-- Membership in a sign vector. -/
private lemma mem_sgn {f : ℕ → ℂ → ℝ} {N : ℕ} {z : ℂ} {i : ℕ} : i ∈ sgn f N z ↔ i < N ∧ 0 < f i z := by
  simp [sgn]

section general

variable {U : Set ℂ} {f : ℕ → ℂ → ℝ}
  (hUo : IsOpen U) (hUc : Convex ℝ U)
  (hfa : ∀ i (z w : ℂ) (r : ℝ), f i (z + r * (w - z)) = f i z + r * (f i w - f i z))
  (hfc : ∀ i, Continuous (f i))

include hUc hfa in
/-- Cells are convex. -/
private lemma cell_convex_step {N : ℕ} {z₁ z₂ : ℂ} (h₁ : z₁ ∈ cellSet U f N) (h₂ : z₂ ∈ cellSet U f N)
    (hs : sgn f N z₁ = sgn f N z₂) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    z₁ + r * (z₂ - z₁) ∈ cellSet U f N ∧ sgn f N (z₁ + r * (z₂ - z₁)) = sgn f N z₁ := by
  have hmemU : z₁ + r * (z₂ - z₁) ∈ U := by
    have := hUc.add_smul_sub_mem h₁.1 h₂.1 ⟨hr0, hr1⟩
    simpa [Complex.real_smul] using this
  have key : ∀ i < N, (0 < f i (z₁ + r * (z₂ - z₁)) ∧ 0 < f i z₁) ∨
      (f i (z₁ + r * (z₂ - z₁)) < 0 ∧ f i z₁ < 0) := by
    intro i hi
    rw [hfa]
    have e1 := h₁.2 i hi
    have e2 := h₂.2 i hi
    have hiff : 0 < f i z₁ ↔ 0 < f i z₂ := by
      have := congrArg (fun s => i ∈ s) hs
      simp only [mem_sgn, eq_iff_iff] at this
      constructor
      · intro h; exact (this.mp ⟨hi, h⟩).2
      · intro h; exact (this.mpr ⟨hi, h⟩).2
    rcases lt_or_gt_of_ne e1 with h | h
    · right
      have h2' : f i z₂ < 0 := by
        rcases lt_or_gt_of_ne e2 with h' | h'
        · exact h'
        · exact absurd (hiff.mpr h') (not_lt.mpr h.le)
      refine ⟨?_, h⟩
      rcases le_total (f i z₁) (f i z₂) with hh | hh
      · nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hh)]
      · nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hh)]
    · left
      have h2' : 0 < f i z₂ := hiff.mp h
      refine ⟨?_, h⟩
      rcases le_total (f i z₁) (f i z₂) with hh | hh
      · nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hh)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hh)]
  refine ⟨⟨hmemU, fun i hi => ?_⟩, ?_⟩
  · rcases key i hi with ⟨h, _⟩ | ⟨h, _⟩
    · exact h.ne'
    · exact h.ne
  · ext i
    simp only [mem_sgn]
    constructor
    · rintro ⟨hi, h⟩
      refine ⟨hi, ?_⟩
      rcases key i hi with ⟨_, h'⟩ | ⟨h', _⟩
      · exact h'
      · exact absurd h (not_lt.mpr h'.le)
    · rintro ⟨hi, h⟩
      refine ⟨hi, ?_⟩
      rcases key i hi with ⟨h', _⟩ | ⟨_, h'⟩
      · exact h'
      · exact absurd h (not_lt.mpr h'.le)

include hUo hfc in
/-- Each point of `cellSet` has an open neighbourhood inside its cell. -/
private lemma cell_open_nhd {N : ℕ} {z : ℂ} (hz : z ∈ cellSet U f N) :
    ∃ O : Set ℂ, IsOpen O ∧ z ∈ O ∧ ∀ y ∈ O, y ∈ cellSet U f N ∧ sgn f N y = sgn f N z := by
  refine ⟨U ∩ ⋂ i ∈ Finset.range N, {y | 0 < f i y * f i z}, ?_, ?_, ?_⟩
  · refine hUo.inter ?_
    refine isOpen_biInter_finset fun i _ => ?_
    exact isOpen_lt continuous_const ((hfc i).mul continuous_const)
  · refine ⟨hz.1, ?_⟩
    simp only [mem_iInter, Finset.mem_range, mem_ofPred_eq]
    intro i hi
    have := hz.2 i hi
    exact mul_self_pos.mpr this
  · intro y hy
    simp only [mem_inter_iff, mem_iInter, Finset.mem_range, mem_ofPred_eq] at hy
    refine ⟨⟨hy.1, fun i hi h => ?_⟩, ?_⟩
    · have := hy.2 i hi
      rw [h, zero_mul] at this
      exact lt_irrefl _ this
    · ext i
      simp only [mem_sgn]
      constructor
      · rintro ⟨hi, h⟩
        refine ⟨hi, ?_⟩
        have := hy.2 i hi
        exact (pos_and_pos_or_neg_and_neg_of_mul_pos this).elim (fun h => h.2)
          (fun h' => absurd h (not_lt.mpr h'.1.le))
      · rintro ⟨hi, h⟩
        refine ⟨hi, ?_⟩
        have := hy.2 i hi
        exact (pos_and_pos_or_neg_and_neg_of_mul_pos this).elim (fun h => h.1)
          (fun h' => absurd h (not_lt.mpr h'.2.le))

include hUo hUc hfa hfc in
/-- Connected components of the complement of the lines are the realized sign vectors. -/
private theorem card_cc_eq (N : ℕ) :
    Nat.card (ConnectedComponents (cellSet U f N)) = (sgn f N '' cellSet U f N).ncard := by
  set X := cellSet U f N
  let g : X → Finset ℕ := fun x => sgn f N x
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨O, hO, hxO, hOs⟩ := cell_open_nhd hUo hfc x.2
    refine ⟨Subtype.val ⁻¹' O, hO.preimage continuous_subtype_val, hxO, fun y hy => ?_⟩
    exact (hOs y hy).2
  have hfib : ∀ x : X, IsPreconnected {y : X | g y = g x} := by
    intro x
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    apply Convex.isPreconnected
    intro a ha b hb s t hs ht hst
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [mem_ofPred_eq, g] at ha' hb'
    have hst' : s = 1 - t := by linarith
    have := cell_convex_step hUc hfa a'.2 b'.2 (ha'.trans hb'.symm) ht (by linarith)
    have e : s • (a' : ℂ) + t • (b' : ℂ) = (a' : ℂ) + t * ((b' : ℂ) - a') := by
      rw [hst', Complex.real_smul, Complex.real_smul]; push_cast; ring
    rw [e]
    refine ⟨⟨_, this.1⟩, ?_, rfl⟩
    simp only [mem_ofPred_eq, g]
    rw [this.2]
    exact ha'
  have hinj : ∀ x y : X, g x = g y → (ConnectedComponents.mk x = ConnectedComponents.mk y) := by
    intro x y h
    rw [ConnectedComponents.coe_eq_coe']
    have hsub := (hfib y).subset_connectedComponent (show y ∈ {z : X | g z = g y} from rfl)
    exact hsub h
  have hconst : ∀ x y : X, ConnectedComponents.mk x = ConnectedComponents.mk y → g x = g y := by
    intro x y h
    rw [ConnectedComponents.coe_eq_coe'] at h
    exact hg.apply_eq_of_isPreconnected isPreconnected_connectedComponent h mem_connectedComponent
  let F : ConnectedComponents X → Set.range g :=
    Quotient.lift (fun x => (⟨g x, x, rfl⟩ : Set.range g)) (fun a b hab => by
      apply Subtype.ext
      exact hconst a b (Quotient.sound hab))
  have hF : Function.Bijective F := by
    constructor
    · intro p q hpq
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe p
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe q
      apply hinj
      have := congrArg Subtype.val hpq
      exact this
    · rintro ⟨_, x, rfl⟩
      exact ⟨ConnectedComponents.mk x, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective F hF), Nat.card_coe_set_eq]
  congr 1
  ext σ
  simp only [mem_range, mem_image, g]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩

/-- Sign vector with one more line. -/
private lemma sgn_succ (N : ℕ) (z : ℂ) :
    sgn f (N + 1) z = if 0 < f N z then insert N (sgn f N z) else sgn f N z := by
  unfold sgn
  rw [Finset.range_add_one, Finset.filter_insert]

/-- Sign vectors are subsets of `range N`. -/
private lemma sgn_subset (N : ℕ) (z : ℂ) : sgn f N z ⊆ Finset.range N := Finset.filter_subset _ _

/-- There are finitely many sign vectors. -/
private lemma finite_sgn_image (N : ℕ) (S : Set ℂ) : (sgn f N '' S).Finite := by
  refine Set.Finite.subset (Finset.finite_toSet (Finset.range N).powerset) ?_
  rintro σ ⟨z, _, rfl⟩
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
  exact sgn_subset (f := f) N z

include hUo hfa hfc in
/-- A cell meeting the next line contains points on both of its sides. -/
private lemma perturb {N : ℕ} (hne : ∃ w, f N w ≠ 0) {z : ℂ} (hz : z ∈ cellSet U f N) (hz0 : f N z = 0) :
    (∃ y ∈ cellSet U f N, sgn f N y = sgn f N z ∧ 0 < f N y) ∧
    (∃ y ∈ cellSet U f N, sgn f N y = sgn f N z ∧ f N y < 0) := by
  obtain ⟨w, hw⟩ := hne
  obtain ⟨O, hO, hzO, hOs⟩ := cell_open_nhd hUo hfc hz
  let p : ℝ → ℂ := fun e => z + e * (w - z)
  have hp : Continuous p := by fun_prop
  have hpO : IsOpen (p ⁻¹' O) := hO.preimage hp
  have h0 : (0 : ℝ) ∈ p ⁻¹' O := by simp [p, hzO]
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hpO 0 h0
  have hin : ∀ e : ℝ, |e| < δ → p e ∈ O := by
    intro e he
    apply hball
    simpa [Metric.mem_ball, Real.dist_eq] using he
  have hval : ∀ e : ℝ, f N (p e) = e * f N w := by
    intro e
    simp only [p]
    rw [hfa, hz0]; ring
  have h1 := hOs _ (hin (δ / 2) (by rw [abs_of_pos (by positivity)]; linarith))
  have h2 := hOs _ (hin (-(δ / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith))
  rcases lt_or_gt_of_ne hw with hw' | hw'
  · refine ⟨⟨_, h2.1, h2.2, ?_⟩, ⟨_, h1.1, h1.2, ?_⟩⟩
    · rw [hval]; nlinarith
    · rw [hval]; nlinarith
  · refine ⟨⟨_, h1.1, h1.2, ?_⟩, ⟨_, h2.1, h2.2, ?_⟩⟩
    · rw [hval]; nlinarith
    · rw [hval]; nlinarith

include hUo hUc hfa hfc in
/-- Adding one line adds as many cells as there are cells it meets. -/
private theorem ncard_step (N : ℕ) (hne : ∃ w, f N w ≠ 0) :
    (sgn f (N + 1) '' cellSet U f (N + 1)).ncard =
      (sgn f N '' cellSet U f N).ncard + (sgn f N '' (cellSet U f N ∩ {z | f N z = 0})).ncard := by
  set Rp := sgn f N '' {z | z ∈ cellSet U f N ∧ 0 < f N z} with hRp
  set Rm := sgn f N '' {z | z ∈ cellSet U f N ∧ f N z < 0} with hRm
  have e1 : sgn f (N + 1) '' cellSet U f (N + 1) = (insert N) '' Rp ∪ Rm := by
    ext σ
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzN : z ∈ cellSet U f N := ⟨hz.1, fun i hi => hz.2 i (by omega)⟩
      have hne' : f N z ≠ 0 := hz.2 N (by omega)
      rw [sgn_succ]
      split_ifs with h
      · left; exact ⟨_, ⟨z, ⟨hzN, h⟩, rfl⟩, rfl⟩
      · right; exact ⟨z, ⟨hzN, lt_of_le_of_ne (not_lt.mp h) hne'⟩, rfl⟩
    · rintro (⟨_, ⟨z, ⟨hz, h⟩, rfl⟩, rfl⟩ | ⟨z, ⟨hz, h⟩, rfl⟩)
      · refine ⟨z, ⟨hz.1, fun i hi => ?_⟩, ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact hz.2 i hi
          · exact h.ne'
        · rw [sgn_succ, if_pos h]
      · refine ⟨z, ⟨hz.1, fun i hi => ?_⟩, ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact hz.2 i hi
          · exact h.ne
        · rw [sgn_succ, if_neg (not_lt.mpr h.le)]
  have hdisj : Disjoint ((insert N) '' Rp) Rm := by
    rw [Set.disjoint_left]
    rintro σ ⟨_, ⟨z, _, rfl⟩, rfl⟩ ⟨y, _, hy⟩
    have : N ∈ sgn f N y := by rw [hy]; exact Finset.mem_insert_self _ _
    have := sgn_subset N y this
    simp at this
  have hinj : Set.InjOn (insert N) Rp := by
    rintro σ ⟨z, _, rfl⟩ τ ⟨y, _, rfl⟩ h
    have hz : N ∉ sgn f N z := fun hh => by simpa using sgn_subset N z hh
    have hy : N ∉ sgn f N y := fun hh => by simpa using sgn_subset N y hh
    have := congrArg (fun s => Finset.erase s N) h
    simpa [Finset.erase_insert hz, Finset.erase_insert hy] using this
  have hunion : Rp ∪ Rm = sgn f N '' cellSet U f N := by
    ext σ
    constructor
    · rintro (⟨z, ⟨hz, _⟩, rfl⟩ | ⟨z, ⟨hz, _⟩, rfl⟩) <;> exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rcases lt_trichotomy (f N z) 0 with h | h | h
      · right; exact ⟨z, ⟨hz, h⟩, rfl⟩
      · obtain ⟨⟨y, hy, hys, hyp⟩, _⟩ := perturb hUo hfa hfc hne hz h
        left; exact ⟨y, ⟨hy, hyp⟩, hys⟩
      · left; exact ⟨z, ⟨hz, h⟩, rfl⟩
  have hinter : Rp ∩ Rm = sgn f N '' (cellSet U f N ∩ {z | f N z = 0}) := by
    ext σ
    constructor
    · rintro ⟨⟨z₁, ⟨h₁, hp⟩, rfl⟩, ⟨z₂, ⟨h₂, hm⟩, hs⟩⟩
      set r : ℝ := f N z₁ / (f N z₁ - f N z₂)
      have hd : 0 < f N z₁ - f N z₂ := by linarith
      have hr0 : 0 ≤ r := div_nonneg hp.le hd.le
      have hr1 : r ≤ 1 := by rw [div_le_one hd]; linarith
      have hc := cell_convex_step hUc hfa h₁ h₂ hs.symm hr0 hr1
      refine ⟨_, ⟨hc.1, ?_⟩, hc.2⟩
      show f N (z₁ + r * (z₂ - z₁)) = 0
      rw [hfa]
      simp only [r]
      field_simp
      ring
    · rintro ⟨z, ⟨hz, h0⟩, rfl⟩
      obtain ⟨⟨y, hy, hys, hyp⟩, ⟨y', hy', hys', hym⟩⟩ := perturb hUo hfa hfc hne hz h0
      exact ⟨⟨y, ⟨hy, hyp⟩, hys⟩, ⟨y', ⟨hy', hym⟩, hys'⟩⟩
  have fRp : Rp.Finite := finite_sgn_image N _
  have fRm : Rm.Finite := finite_sgn_image N _
  rw [e1, Set.ncard_union_eq hdisj (fRp.image _) fRm, hinj.ncard_image, ← hunion, ← hinter,
    Set.ncard_union_add_ncard_inter _ _ fRp fRm]

/-! One-dimensional count: sign vectors of affine functions along an interval. -/

/-- Sign vector along a line. -/
private noncomputable def sgn1 (N : ℕ) (c d : ℕ → ℝ) (x : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun j => 0 < c j + x * d j)

/-- The sign vector is constant on an interval without roots. -/
private lemma sgn1_const {N : ℕ} {c d : ℕ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (h : ∀ z, x ≤ z → z ≤ y → ∀ j < N, c j + z * d j ≠ 0) : sgn1 N c d x = sgn1 N c d y := by
  ext j
  simp only [sgn1, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hx⟩
    refine ⟨hj, ?_⟩
    by_contra hy
    replace hy := not_lt.mp hy
    have hcont : ContinuousOn (fun z => c j + z * d j) (Set.Icc x y) := by fun_prop
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hxy hcont ⟨hy, hx.le⟩
    exact h z hz.1 hz.2 j hj hz0
  · rintro ⟨hj, hy⟩
    refine ⟨hj, ?_⟩
    by_contra hx
    replace hx := not_lt.mp hx
    have hcont : ContinuousOn (fun z => c j + z * d j) (Set.Icc x y) := by fun_prop
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hxy hcont ⟨hx, hy.le⟩
    exact h z hz.1 hz.2 j hj hz0

/-- The sign vector changes across a root. -/
private lemma sgn1_sep {N : ℕ} {c d : ℕ → ℝ} {x y r : ℝ} (hxr : x < r) (hry : r < y) {j : ℕ} (hj : j < N)
    (hr : c j + r * d j = 0) (hx : c j + x * d j ≠ 0) (_hy : c j + y * d j ≠ 0) :
    sgn1 N c d x ≠ sgn1 N c d y := by
  have hc : c j = - r * d j := by linarith
  have hd : d j ≠ 0 := by
    intro h; apply hx; rw [hc, h]; ring
  intro heq
  have := congrArg (fun s => j ∈ s) heq
  simp only [sgn1, Finset.mem_filter, Finset.mem_range, eq_iff_iff] at this
  rw [hc] at this
  rcases lt_or_gt_of_ne hd with h | h
  · have h1 : 0 < -r * d j + x * d j := by nlinarith
    have h2 : -r * d j + y * d j < 0 := by nlinarith
    exact absurd (this.mp ⟨hj, h1⟩).2 (not_lt.mpr h2.le)
  · have h1 : -r * d j + x * d j < 0 := by nlinarith
    have h2 : 0 < -r * d j + y * d j := by nlinarith
    exact absurd (this.mpr ⟨hj, h2⟩).2 (not_lt.mpr h1.le)

/-- There are finitely many one-dimensional sign vectors. -/
private lemma finite_sgn1_image (N : ℕ) (c d : ℕ → ℝ) (S : Set ℝ) : (sgn1 N c d '' S).Finite := by
  refine Set.Finite.subset (Finset.finite_toSet (Finset.range N).powerset) ?_
  rintro σ ⟨z, _, rfl⟩
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
  exact Finset.filter_subset _ _

/-- On a root-free open interval there is exactly one sign vector. -/
private lemma sgn1_image_Ioo {N : ℕ} {c d : ℕ → ℝ} {a b : ℝ} (hab : a < b)
    (h : ∀ z, a < z → z < b → ∀ j < N, c j + z * d j ≠ 0) :
    sgn1 N c d '' {x | a < x ∧ x < b ∧ ∀ j < N, c j + x * d j ≠ 0} = {sgn1 N c d ((a + b) / 2)} := by
  ext σ
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, ⟨hax, hxb, _⟩, rfl⟩
    rcases le_total x ((a + b) / 2) with hx | hx
    · exact sgn1_const hx (fun z h1 h2 => h z (by linarith) (by linarith))
    · exact (sgn1_const hx (fun z h1 h2 => h z (by linarith) (by linarith))).symm
  · rintro rfl
    exact ⟨(a + b) / 2, ⟨by linarith, by linarith, h _ (by linarith) (by linarith)⟩, rfl⟩

/-- The number of sign vectors along an interval is one more than the number of roots. -/
private theorem sgn1_count (N : ℕ) (c d : ℕ → ℝ) (a : ℝ) (Rt : Finset ℝ) :
    ∀ b, a < b → (∀ x, x ∈ Rt ↔ (a < x ∧ x < b ∧ ∃ j < N, c j + x * d j = 0)) →
      (sgn1 N c d '' {x | a < x ∧ x < b ∧ ∀ j < N, c j + x * d j ≠ 0}).ncard = Rt.card + 1 := by
  induction Rt using Finset.induction_on_max with
  | empty =>
    intro b hab hR
    have h : ∀ z, a < z → z < b → ∀ j < N, c j + z * d j ≠ 0 := by
      intro z h1 h2 j hj h0
      have := (hR z).mpr ⟨h1, h2, j, hj, h0⟩
      simp at this
    rw [sgn1_image_Ioo hab h, Set.ncard_singleton]
    simp
  | insert r s hs ih =>
    intro b hab hR
    have hr := (hR r).mp (Finset.mem_insert_self r s)
    obtain ⟨har, hrb, j₀, hj₀, hr0⟩ := hr
    have hrs : r ∉ s := fun h => lt_irrefl r (hs r h)
    have ih' := ih r har (by
      intro x
      constructor
      · intro hx
        obtain ⟨h1, _, h3⟩ := (hR x).mp (Finset.mem_insert_of_mem hx)
        exact ⟨h1, hs x hx, h3⟩
      · rintro ⟨h1, h2, h3⟩
        have := (hR x).mpr ⟨h1, by linarith, h3⟩
        rcases Finset.mem_insert.mp this with h | h
        · exact absurd h h2.ne
        · exact h)
    have hno : ∀ z, r < z → z < b → ∀ j < N, c j + z * d j ≠ 0 := by
      intro z h1 h2 j hj h0
      have := (hR z).mpr ⟨by linarith, h2, j, hj, h0⟩
      rcases Finset.mem_insert.mp this with h | h
      · exact absurd h h1.ne'
      · exact absurd (hs z h) (not_lt.mpr h1.le)
    have hsplit : {x | a < x ∧ x < b ∧ ∀ j < N, c j + x * d j ≠ 0} =
        {x | a < x ∧ x < r ∧ ∀ j < N, c j + x * d j ≠ 0} ∪
          {x | r < x ∧ x < b ∧ ∀ j < N, c j + x * d j ≠ 0} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rcases lt_trichotomy x r with h | rfl | h
        · left; exact ⟨h1, h, h3⟩
        · exact absurd hr0 (h3 j₀ hj₀)
        · right; exact ⟨h, h2, h3⟩
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
        · exact ⟨h1, by linarith, h3⟩
        · exact ⟨by linarith, h2, h3⟩
    rw [hsplit, Set.image_union, sgn1_image_Ioo hrb hno, Set.union_singleton,
      Set.ncard_insert_of_notMem _ (finite_sgn1_image N c d _), ih', Finset.card_insert_of_notMem hrs]
    rintro ⟨x, ⟨h1, h2, h3⟩, hx⟩
    apply sgn1_sep h2 (show r < (r + b) / 2 by linarith) hj₀ hr0 (h3 j₀ hj₀)
      (hno _ (by linarith) (by linarith) j₀ hj₀) hx

include hUo hUc hfa hfc in
/-- **Counting regions.** Lines `f i = 0` (in a fixed order) each meet the open convex set `U`
in an open segment `A i + r (B i - A i)`, `0 < r < 1`; then the number of regions is
`1 + ∑ (1 + number of distinct points of segment `i` on earlier lines)`. -/
private theorem count_general (hne : U.Nonempty) (A B : ℕ → ℂ) (N : ℕ)
    (hline : ∀ i < N, ∀ z, z ∈ U → f i z = 0 → ∃ r : ℝ, 0 < r ∧ r < 1 ∧ z = A i + r * (B i - A i))
    (hseg : ∀ i < N, ∀ (r : ℝ), 0 < r → r < 1 →
      A i + r * (B i - A i) ∈ U ∧ f i (A i + r * (B i - A i)) = 0)
    (hnz : ∀ i < N, ∃ w, f i w ≠ 0)
    (hnc : ∀ i < N, ∀ j < i, ∃ r : ℝ, f j (A i + r * (B i - A i)) ≠ 0) :
    Nat.card (ConnectedComponents (cellSet U f N)) =
      1 + ∑ i ∈ Finset.range N,
        (1 + {r : ℝ | 0 < r ∧ r < 1 ∧ ∃ j < i, f j (A i + r * (B i - A i)) = 0}.ncard) := by
  rw [card_cc_eq hUo hUc hfa hfc]
  suffices H : ∀ M ≤ N, (sgn f M '' cellSet U f M).ncard = 1 + ∑ i ∈ Finset.range M,
      (1 + {r : ℝ | 0 < r ∧ r < 1 ∧ ∃ j < i, f j (A i + r * (B i - A i)) = 0}.ncard) from
    H N le_rfl
  intro M hM
  induction M with
  | zero =>
    obtain ⟨z₀, hz₀⟩ := hne
    have : sgn f 0 '' cellSet U f 0 = {∅} := by
      ext σ
      simp only [Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, _, rfl⟩; simp [sgn]
      · rintro rfl; exact ⟨z₀, ⟨hz₀, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, by simp [sgn]⟩
    rw [this, Set.ncard_singleton]
    simp
  | succ N ih =>
    rw [ncard_step hUo hUc hfa hfc N (hnz N (by omega)), ih (by omega), Finset.sum_range_succ]
    set c : ℕ → ℝ := fun j => f j (A N)
    set d : ℕ → ℝ := fun j => f j (B N) - f j (A N)
    have hγ : ∀ j (r : ℝ), f j (A N + r * (B N - A N)) = c j + r * d j := fun j r => hfa j _ _ r
    have hM : sgn f N '' (cellSet U f N ∩ {z | f N z = 0}) =
        sgn1 N c d '' {x | 0 < x ∧ x < 1 ∧ ∀ j < N, c j + x * d j ≠ 0} := by
      ext σ
      constructor
      · rintro ⟨z, ⟨⟨hzU, hz⟩, hz0⟩, rfl⟩
        obtain ⟨r, hr0, hr1, rfl⟩ := hline N (by omega) z hzU hz0
        refine ⟨r, ⟨hr0, hr1, fun j hj => ?_⟩, ?_⟩
        · rw [← hγ]; exact hz j hj
        · ext j; simp [sgn, sgn1, hγ]
      · rintro ⟨r, ⟨hr0, hr1, hr⟩, rfl⟩
        obtain ⟨hU, h0⟩ := hseg N (by omega) r hr0 hr1
        refine ⟨A N + r * (B N - A N), ⟨⟨hU, fun j hj => ?_⟩, h0⟩, ?_⟩
        · rw [hγ]; exact hr j hj
        · ext j; simp [sgn, sgn1, hγ]
    have hfin : {r : ℝ | 0 < r ∧ r < 1 ∧ ∃ j < N, f j (A N + r * (B N - A N)) = 0}.Finite := by
      refine Set.Finite.subset ((Finset.range N).finite_toSet.biUnion
        (fun j _ => Set.finite_singleton (-(c j) / d j))) ?_
      rintro x ⟨_, _, j, hj, hx⟩
      simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_singleton_iff]
      refine ⟨j, hj, ?_⟩
      rw [hγ] at hx
      obtain ⟨r, hr⟩ := hnc N (by omega) j hj
      rw [hγ] at hr
      have hd : d j ≠ 0 := by
        intro h
        apply hr
        have : c j = 0 := by rw [h] at hx; linarith
        rw [this, h]; ring
      field_simp
      linarith
    rw [hM, sgn1_count N c d 0 hfin.toFinset 1 one_pos (by
      intro x
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hγ]), Set.ncard_eq_toFinset_card _ hfin]
    ring

end general

/-! ### Trigonometric layer -/

/-- `E α = exp (α i)`. -/
private noncomputable def E (α : ℝ) : ℂ := Complex.exp (α * Complex.I)

/-- Real part of `E α`. -/
private lemma E_re (α : ℝ) : (E α).re = Real.cos α := Complex.exp_ofReal_mul_I_re α
/-- Imaginary part of `E α`. -/
private lemma E_im (α : ℝ) : (E α).im = Real.sin α := Complex.exp_ofReal_mul_I_im α

/-- `E α E β = E (α + β)`. -/
private lemma E_mul (α β : ℝ) : E α * E β = E (α + β) := by
  unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- Conjugate of `E α`. -/
private lemma E_conj (α : ℝ) : (starRingEnd ℂ) (E α) = E (-α) := by
  unfold E; rw [← Complex.exp_conj]; congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

/-- `E 0 = 1`. -/
private lemma E_zero : E 0 = 1 := by simp [E]

/-- Half the central angle, `π / n`. -/
private noncomputable def ph (n : ℕ) : ℝ := Real.pi / n

/-- The vertices in terms of `E`. -/
private lemma vertex_eq (n j : ℕ) : vertex n j = E (j * (2 * ph n)) := by
  unfold vertex E ph; congr 1; push_cast; ring

section basic
variable {n : ℕ} (hn : 3 ≤ n)
include hn

/-- `n > 0` as a real number. -/
private lemma n_pos : (0 : ℝ) < n := by
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- `π / n > 0`. -/
private lemma ph_pos : 0 < ph n := div_pos Real.pi_pos (n_pos hn)

/-- `π / n ≤ π / 3` for `n ≥ 3`. -/
private lemma ph_le : ph n ≤ Real.pi / 3 := by
  unfold ph
  apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
  exact_mod_cast hn

/-- `n (π / n) = π`. -/
private lemma n_mul_ph : (n : ℝ) * ph n = Real.pi := by
  unfold ph; field_simp [(n_pos hn).ne']

/-- `sin (π/n) > 0`. -/
private lemma sin_ph_pos : 0 < Real.sin (ph n) :=
  Real.sin_pos_of_pos_of_lt_pi (ph_pos hn) (by linarith [ph_le hn, Real.pi_pos])

/-- `cos (π/n) > 0`. -/
private lemma cos_ph_pos : 0 < Real.cos (ph n) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [ph_pos hn, Real.pi_pos], by linarith [ph_le hn, Real.pi_pos]⟩

/-- `sin (2π/n) > 0`. -/
private lemma sin_two_ph_pos : 0 < Real.sin (2 * ph n) := by
  rw [Real.sin_two_mul]
  have := sin_ph_pos hn
  have := cos_ph_pos hn
  positivity

/-- `1 - cos (2π/n) > 0`. -/
private lemma one_sub_cos_pos : 0 < 1 - Real.cos (2 * ph n) := by
  rw [Real.cos_two_mul_eq_one_sub]
  have := sin_ph_pos hn
  nlinarith

end basic

/-- Frame `x`-coordinate relative to the corner `1` of the rotated polygon. -/
private noncomputable def x0 (n : ℕ) (w : ℂ) : ℝ :=
  ((1 - w.re) / (1 - Real.cos (2 * ph n)) - w.im / Real.sin (2 * ph n)) / 2

/-- Frame `y`-coordinate relative to the corner `1` of the rotated polygon. -/
private noncomputable def y0 (n : ℕ) (w : ℂ) : ℝ :=
  ((1 - w.re) / (1 - Real.cos (2 * ph n)) + w.im / Real.sin (2 * ph n)) / 2

/-- Frame `x`-coordinate at corner `C`: `z = V_C + x (V_{C-1} - V_C) + y (V_{C+1} - V_C)`. -/
private noncomputable def fx (n C : ℕ) (z : ℂ) : ℝ := x0 n ((starRingEnd ℂ) (vertex n C) * z)

/-- Frame `y`-coordinate at corner `C`. -/
private noncomputable def fy (n C : ℕ) (z : ℂ) : ℝ := y0 n ((starRingEnd ℂ) (vertex n C) * z)

/-- Closed form of the frame `x`-coordinate of the vertex at relative position `a`. -/
private noncomputable def Xr (n : ℕ) (a : ℝ) : ℝ :=
  Real.sin (a * ph n) * Real.sin ((a - 1) * ph n) / (Real.sin (ph n) * Real.sin (2 * ph n))

/-- Closed form of the frame `y`-coordinate of the vertex at relative position `a`. -/
private noncomputable def Yr (n : ℕ) (a : ℝ) : ℝ :=
  Real.sin (a * ph n) * Real.sin ((a + 1) * ph n) / (Real.sin (ph n) * Real.sin (2 * ph n))

section frames
variable {n : ℕ} (hn : 3 ≤ n)
include hn

/-- Frame `x`-coordinate of the unit vector at angle `2πa/n` (closed form). -/
private lemma x0_E (a : ℝ) : x0 n (E (a * (2 * ph n))) = Xr n a := by
  have hs := sin_ph_pos hn
  have hc := cos_ph_pos hn
  unfold x0 Xr
  rw [E_re, E_im, show a * (2 * ph n) = 2 * (a * ph n) by ring, Real.cos_two_mul_eq_one_sub,
    Real.cos_two_mul_eq_one_sub, Real.sin_two_mul, Real.sin_two_mul,
    show (a - 1) * ph n = a * ph n - ph n by ring, Real.sin_sub]
  field_simp
  ring

/-- Frame `y`-coordinate of the unit vector at angle `2πa/n` (closed form). -/
private lemma y0_E (a : ℝ) : y0 n (E (a * (2 * ph n))) = Yr n a := by
  have hs := sin_ph_pos hn
  have hc := cos_ph_pos hn
  unfold y0 Yr
  rw [E_re, E_im, show a * (2 * ph n) = 2 * (a * ph n) by ring, Real.cos_two_mul_eq_one_sub,
    Real.cos_two_mul_eq_one_sub, Real.sin_two_mul, Real.sin_two_mul,
    show (a + 1) * ph n = a * ph n + ph n by ring, Real.sin_add]
  field_simp
  ring

omit hn in
/-- Rotating vertex `i` back by vertex `C`. -/
private lemma conj_vertex_mul (C i : ℕ) :
    (starRingEnd ℂ) (vertex n C) * vertex n i = E (((i : ℝ) - C) * (2 * ph n)) := by
  rw [vertex_eq, vertex_eq, E_conj, E_mul]; congr 1; ring

/-- Frame `x`-coordinate of a vertex. -/
private lemma fx_vertex (C i : ℕ) : fx n C (vertex n i) = Xr n ((i : ℝ) - C) := by
  unfold fx; rw [conj_vertex_mul, x0_E hn]

/-- Frame `y`-coordinate of a vertex. -/
private lemma fy_vertex (C i : ℕ) : fy n C (vertex n i) = Yr n ((i : ℝ) - C) := by
  unfold fy; rw [conj_vertex_mul, y0_E hn]

end frames

/-- The frame `x`-coordinate is real-affine. -/
private lemma fx_aff (n C : ℕ) (z p q : ℂ) (r : ℝ) :
    fx n C (z + r * (q - p)) = fx n C z + r * (fx n C q - fx n C p) := by
  unfold fx x0
  rw [show (starRingEnd ℂ) (vertex n C) * (z + r * (q - p)) =
    (starRingEnd ℂ) (vertex n C) * z + (r : ℂ) * ((starRingEnd ℂ) (vertex n C) * q -
      (starRingEnd ℂ) (vertex n C) * p) by ring]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.add_im,
    Complex.im_ofReal_mul, Complex.sub_im]
  ring

/-- The frame `y`-coordinate is real-affine. -/
private lemma fy_aff (n C : ℕ) (z p q : ℂ) (r : ℝ) :
    fy n C (z + r * (q - p)) = fy n C z + r * (fy n C q - fy n C p) := by
  unfold fy y0
  rw [show (starRingEnd ℂ) (vertex n C) * (z + r * (q - p)) =
    (starRingEnd ℂ) (vertex n C) * z + (r : ℂ) * ((starRingEnd ℂ) (vertex n C) * q -
      (starRingEnd ℂ) (vertex n C) * p) by ring]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.add_im,
    Complex.im_ofReal_mul, Complex.sub_im]
  ring

/-- The frame `x`-coordinate is continuous. -/
private lemma fx_cont (n C : ℕ) : Continuous (fx n C) := by
  unfold fx x0; fun_prop

/-- The frame `y`-coordinate is continuous. -/
private lemma fy_cont (n C : ℕ) : Continuous (fy n C) := by
  unfold fy y0; fun_prop

/-- Reconstruction of a point from its frame coordinates at corner `j+1`. -/
private lemma recon {n : ℕ} (hn : 3 ≤ n) (j : ℕ) (z : ℂ) :
    z = vertex n (j + 1) + (fx n (j + 1) z : ℂ) * (vertex n j - vertex n (j + 1)) +
      (fy n (j + 1) z : ℂ) * (vertex n (j + 2) - vertex n (j + 1)) := by
  set V := vertex n (j + 1)
  set w := (starRingEnd ℂ) V * z
  have hVV : V * (starRingEnd ℂ) V = 1 := by
    simp only [V]; rw [vertex_eq, E_conj, E_mul]; simp [E]
  have hz : z = V * w := by simp only [w]; rw [← mul_assoc, hVV, one_mul]
  have hVj : vertex n j = V * E (-(2 * ph n)) := by
    simp only [V]; rw [vertex_eq, vertex_eq, E_mul]; congr 1; push_cast; ring
  have hVj2 : vertex n (j + 2) = V * E (2 * ph n) := by
    simp only [V]; rw [vertex_eq, vertex_eq, E_mul]; congr 1; push_cast; ring
  have hw : w = 1 + (x0 n w : ℂ) * (E (-(2 * ph n)) - 1) + (y0 n w : ℂ) * (E (2 * ph n) - 1) := by
    have h1 := one_sub_cos_pos hn
    have h2 := sin_two_ph_pos hn
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, Complex.sub_re, E_re,
        Real.cos_neg]
      unfold x0 y0
      field_simp
      ring
    · simp only [Complex.add_im, Complex.one_im, Complex.im_ofReal_mul, Complex.sub_im, E_im,
        Real.sin_neg]
      unfold x0 y0
      field_simp
      ring
  show z = V + (x0 n w : ℂ) * (vertex n j - V) + (y0 n w : ℂ) * (vertex n (j + 2) - V)
  rw [hVj, hVj2]
  conv_lhs => rw [hz, hw]
  ring

/-! ### Values and inequalities of the closed forms -/

section values
variable {n : ℕ} (hn : 3 ≤ n)
include hn

/-- `Xr` has period `n`. -/
private lemma Xr_periodic : Function.Periodic (Xr n) n := by
  intro a
  unfold Xr
  rw [show (a + n) * ph n = a * ph n + Real.pi by rw [add_mul, n_mul_ph hn],
    show (a + n - 1) * ph n = (a - 1) * ph n + Real.pi by rw [sub_mul, add_mul, n_mul_ph hn]; ring,
    Real.sin_add_pi, Real.sin_add_pi]
  ring

/-- `Yr` has period `n`. -/
private lemma Yr_periodic : Function.Periodic (Yr n) n := by
  intro a
  unfold Yr
  rw [show (a + n) * ph n = a * ph n + Real.pi by rw [add_mul, n_mul_ph hn],
    show (a + n + 1) * ph n = (a + 1) * ph n + Real.pi by rw [add_mul, add_mul, n_mul_ph hn]; ring,
    Real.sin_add_pi, Real.sin_add_pi]
  ring

/-- `Xr` is invariant under integer multiples of `n`. -/
private lemma Xr_shift (a : ℝ) (q : ℤ) : Xr n (a + q * n) = Xr n a :=
  (Xr_periodic hn).int_mul q a

/-- `Yr` is invariant under integer multiples of `n`. -/
private lemma Yr_shift (a : ℝ) (q : ℤ) : Yr n (a + q * n) = Yr n a :=
  (Yr_periodic hn).int_mul q a

omit hn in
/-- The corner itself: `x = 0`. -/
private lemma Xr_zero : Xr n 0 = 0 := by simp [Xr]
omit hn in
/-- The corner itself: `y = 0`. -/
private lemma Yr_zero : Yr n 0 = 0 := by simp [Yr]
omit hn in
/-- The next vertex: `x = 0`. -/
private lemma Xr_one : Xr n 1 = 0 := by simp [Xr]
/-- The next vertex: `y = 1`. -/
private lemma Yr_one : Yr n 1 = 1 := by
  have := sin_ph_pos hn; have := sin_two_ph_pos hn
  unfold Yr; rw [show ((1 : ℝ) + 1) * ph n = 2 * ph n by ring, one_mul]; field_simp
/-- The previous vertex: `x = 1`. -/
private lemma Xr_neg_one : Xr n (-1) = 1 := by
  have := sin_ph_pos hn; have := sin_two_ph_pos hn
  unfold Xr
  rw [show ((-1 : ℝ) - 1) * ph n = -(2 * ph n) by ring, show (-1 : ℝ) * ph n = -(ph n) by ring,
    Real.sin_neg, Real.sin_neg]
  field_simp
omit hn in
/-- The previous vertex: `y = 0`. -/
private lemma Yr_neg_one : Yr n (-1) = 0 := by simp [Yr]
/-- The vertex two steps ahead: `x = 1`. -/
private lemma Xr_two : Xr n 2 = 1 := by
  have := sin_ph_pos hn; have := sin_two_ph_pos hn
  unfold Xr; rw [show ((2 : ℝ) - 1) * ph n = ph n by ring]; field_simp
/-- The vertex two steps back: `y = 1`. -/
private lemma Yr_neg_two : Yr n (-2) = 1 := by
  have := sin_ph_pos hn; have := sin_two_ph_pos hn
  unfold Yr
  rw [show ((-2 : ℝ) + 1) * ph n = -(ph n) by ring, show (-2 : ℝ) * ph n = -(2 * ph n) by ring,
    Real.sin_neg, Real.sin_neg]
  field_simp
omit hn in
/-- The vertex two steps ahead: `y = W`. -/
private lemma Yr_two_eq : Yr n 2 = Xr n (-2) := by
  unfold Xr Yr
  rw [show ((-2 : ℝ) - 1) * ph n = -((2 + 1) * ph n) by ring,
    show (-2 : ℝ) * ph n = -(2 * ph n) by ring, Real.sin_neg, Real.sin_neg]
  ring

/-- `W = Xr (-2) = 1 + 2 cos (2π/n)`. -/
private lemma Xr_neg_two : Xr n (-2) = 1 + 2 * Real.cos (2 * ph n) := by
  have hs := sin_ph_pos hn; have := sin_two_ph_pos hn
  unfold Xr
  rw [show ((-2 : ℝ) - 1) * ph n = -(3 * ph n) by ring,
    show (-2 : ℝ) * ph n = -(2 * ph n) by ring, Real.sin_neg, Real.sin_neg, Real.sin_three_mul,
    Real.cos_two_mul_eq_one_sub]
  field_simp
  ring

/-- Basic inequalities at relative positions `1 ≤ b ≤ n - 1`. -/
private lemma XY_basic (b : ℝ) (hb1 : 1 ≤ b) (hb2 : b ≤ n - 1) :
    0 ≤ Xr n b ∧ 0 ≤ Yr n b ∧ 1 ≤ Xr n b + Yr n b ∧ (b ≤ n - 2 → 0 < Yr n b) := by
  have hs := sin_ph_pos hn
  have hc := cos_ph_pos hn
  have hs2 := sin_two_ph_pos hn
  have hp := ph_pos hn
  have hnp := n_mul_ph hn
  have hD : 0 < Real.sin (ph n) * Real.sin (2 * ph n) := mul_pos hs hs2
  have h1 : 0 < Real.sin (b * ph n) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by nlinarith)
    nlinarith
  have h2 : 0 ≤ Real.sin ((b - 1) * ph n) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith)
    nlinarith
  have h3 : 0 ≤ Real.sin ((b + 1) * ph n) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith)
    nlinarith
  have hge : Real.sin (ph n) ≤ Real.sin (b * ph n) := by
    have := Real.sin_sub_sin (b * ph n) (ph n)
    have e1 : 0 ≤ Real.sin ((b * ph n - ph n) / 2) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith)
      nlinarith
    have e2 : 0 ≤ Real.cos ((b * ph n + ph n) / 2) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> nlinarith
    nlinarith
  refine ⟨div_nonneg (mul_nonneg h1.le h2) hD.le, div_nonneg (mul_nonneg h1.le h3) hD.le, ?_, ?_⟩
  · unfold Xr Yr
    rw [← add_div, le_div_iff₀ hD, one_mul, ← mul_add,
      show (b - 1) * ph n = b * ph n - ph n by ring, show (b + 1) * ph n = b * ph n + ph n by ring,
      Real.sin_sub, Real.sin_add, Real.sin_two_mul]
    nlinarith [mul_le_mul hge hge hs.le h1.le]
  · intro hb3
    apply div_pos _ hD
    apply mul_pos h1
    apply Real.sin_pos_of_pos_of_lt_pi (by nlinarith)
    nlinarith

end values

/-! ### Integer relative positions -/

section intpos
variable {n : ℕ} (hn : 3 ≤ n)
include hn

/-- Shifting a relative position by `n`. -/
private lemma XY_shift1 (ρ : ℤ) : Xr n ρ = Xr n ((ρ + n : ℤ) : ℝ) ∧ Yr n ρ = Yr n ((ρ + n : ℤ) : ℝ) := by
  rw [show ((ρ + n : ℤ) : ℝ) = (ρ : ℝ) + ((1 : ℤ) : ℝ) * n by push_cast; ring, Xr_shift hn,
    Yr_shift hn]
  exact ⟨rfl, rfl⟩

/-- Frame coordinates of the other vertices: `x, y ≥ 0` and `x + y ≥ 1`. -/
private lemma XY_range (ρ : ℤ) (h1 : -(n : ℤ) ≤ ρ) (h2 : ρ ≤ n) (h0 : ρ ≠ 0) (h3 : ρ ≠ n)
    (h4 : ρ ≠ -n) : 0 ≤ Xr n ρ ∧ 0 ≤ Yr n ρ ∧ 1 ≤ Xr n ρ + Yr n ρ := by
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · obtain ⟨e1, e2⟩ := XY_shift1 hn ρ
    rw [e1, e2]
    have hb1 : (1 : ℝ) ≤ ((ρ + n : ℤ) : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ ρ + n by omega)
    have hb2 : ((ρ + n : ℤ) : ℝ) ≤ (n : ℝ) - 1 := by
      have : ((ρ + n : ℤ) : ℝ) ≤ ((n - 1 : ℤ) : ℝ) := by exact_mod_cast (show ρ + n ≤ n - 1 by omega)
      simpa using this
    have h := XY_basic hn _ hb1 hb2
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · have hb1 : (1 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ ρ by omega)
    have hb2 : (ρ : ℝ) ≤ (n : ℝ) - 1 := by
      have : (ρ : ℝ) ≤ ((n - 1 : ℤ) : ℝ) := by exact_mod_cast (show ρ ≤ n - 1 by omega)
      simpa using this
    have h := XY_basic hn _ hb1 hb2
    exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The frame `y`-coordinate vanishes only on the two vertices of the previous side. -/
private lemma Y_pos_range (ρ : ℤ) (h1 : -(n : ℤ) ≤ ρ) (h2 : ρ ≤ n) (h0 : ρ ≠ 0) (h3 : ρ ≠ n)
    (h4 : ρ ≠ -n) (h5 : ρ ≠ -1) (h6 : ρ ≠ n - 1) : 0 < Yr n ρ := by
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · obtain ⟨_, e2⟩ := XY_shift1 hn ρ
    rw [e2]
    have hb1 : (1 : ℝ) ≤ ((ρ + n : ℤ) : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ ρ + n by omega)
    have hb2 : ((ρ + n : ℤ) : ℝ) ≤ (n : ℝ) - 1 := by
      have : ((ρ + n : ℤ) : ℝ) ≤ ((n - 1 : ℤ) : ℝ) := by exact_mod_cast (show ρ + n ≤ n - 1 by omega)
      simpa using this
    have hb3 : ((ρ + n : ℤ) : ℝ) ≤ (n : ℝ) - 2 := by
      have : ((ρ + n : ℤ) : ℝ) ≤ ((n - 2 : ℤ) : ℝ) := by exact_mod_cast (show ρ + n ≤ n - 2 by omega)
      simpa using this
    exact (XY_basic hn _ hb1 hb2).2.2.2 hb3
  · have hb1 : (1 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ ρ by omega)
    have hb2 : (ρ : ℝ) ≤ (n : ℝ) - 1 := by
      have : (ρ : ℝ) ≤ ((n - 1 : ℤ) : ℝ) := by exact_mod_cast (show ρ ≤ n - 1 by omega)
      simpa using this
    have hb3 : (ρ : ℝ) ≤ (n : ℝ) - 2 := by
      have : (ρ : ℝ) ≤ ((n - 2 : ℤ) : ℝ) := by exact_mod_cast (show ρ ≤ n - 2 by omega)
      simpa using this
    exact (XY_basic hn _ hb1 hb2).2.2.2 hb3

/-- All vertices have nonnegative frame coordinates. -/
private lemma XY_nonneg (ρ : ℤ) (h1 : -(n : ℤ) ≤ ρ) (h2 : ρ ≤ n) : 0 ≤ Xr n ρ ∧ 0 ≤ Yr n ρ := by
  by_cases h0 : ρ = 0
  · subst h0; simp [Xr_zero, Yr_zero]
  by_cases h3 : ρ = n
  · subst h3
    rw [show ((n : ℤ) : ℝ) = (0 : ℝ) + ((1 : ℤ) : ℝ) * n by push_cast; ring, Xr_shift hn,
      Yr_shift hn, Xr_zero, Yr_zero]
    simp
  by_cases h4 : ρ = -n
  · subst h4
    rw [show ((-(n : ℤ) : ℤ) : ℝ) = (0 : ℝ) + ((-1 : ℤ) : ℝ) * n by push_cast; ring, Xr_shift hn,
      Yr_shift hn, Xr_zero, Yr_zero]
    simp
  have h := XY_range hn ρ h1 h2 h0 h3 h4
  exact ⟨h.1, h.2.1⟩

/-- Frame `x`-coordinate of a vertex, as an integer relative position. -/
private lemma fx_vertex_int (C i : ℕ) : fx n C (vertex n i) = Xr n (((i : ℤ) - C : ℤ) : ℝ) := by
  rw [fx_vertex hn]; push_cast; rfl

/-- Frame `y`-coordinate of a vertex, with an integer relative position. -/
private lemma fy_vertex_int (C i : ℕ) : fy n C (vertex n i) = Yr n (((i : ℤ) - C : ℤ) : ℝ) := by
  rw [fy_vertex hn]; push_cast; rfl

/-- `W = 1 + 2 cos (2π/n) ≥ 0`. -/
private lemma W_nonneg : 0 ≤ Xr n (-2) := by
  have := XY_range hn (-2) (by omega) (by omega) (by omega) (by omega) (by omega)
  simpa using this.1

end intpos

/-- Vertices are periodic with period `n`. -/
private lemma vertex_add_n (n i : ℕ) (hn : 0 < n) : vertex n (i + n) = vertex n i := by
  unfold vertex
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((i + n : ℕ) : ℂ) / (n : ℂ) =
    2 * Real.pi * Complex.I * (i : ℂ) / n + (1 : ℕ) * (2 * Real.pi * Complex.I) by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast; field_simp]
  rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- Every vertex lies in the polygon. -/
private lemma vertex_mem_polygon (n i : ℕ) (hn : 0 < n) : vertex n i ∈ polygon n := by
  apply subset_convexHull
  refine ⟨⟨i % n, Nat.mod_lt _ hn⟩, ?_⟩
  simp only
  conv_rhs => rw [← Nat.mod_add_div i n]
  induction (i / n) with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← add_assoc, vertex_add_n n _ hn, ih]

/-! ### The polygon in the frames -/

section polygon
variable {n : ℕ} (hn : 3 ≤ n)
include hn

/-- The polygon lies in the angle of each corner. -/
private lemma polygon_sub (j : ℕ) (hj : j < n) :
    polygon n ⊆ {z | 0 ≤ fx n (j + 1) z ∧ 0 ≤ fy n (j + 1) z} := by
  apply convexHull_min
  · rintro _ ⟨i, rfl⟩
    simp only [mem_ofPred_eq]
    rw [fx_vertex_int hn, fy_vertex_int hn]
    exact XY_nonneg hn _ (by omega) (by omega)
  · intro x hx y hy a b ha hb hab
    simp only [mem_ofPred_eq] at hx hy ⊢
    have e : a • x + b • y = x + (b : ℂ) * (y - x) := by
      rw [Complex.real_smul, Complex.real_smul, show (a : ℂ) = 1 - b by
        rw [show a = 1 - b by linarith]; push_cast; ring]
      ring
    rw [e, fx_aff, fy_aff]
    constructor <;> nlinarith

/-- Interior points have positive frame coordinates at every corner. -/
private lemma interior_pos (j : ℕ) (hj : j < n) {z : ℂ} (hz : z ∈ interior (polygon n)) :
    0 < fx n (j + 1) z ∧ 0 < fy n (j + 1) z := by
  have key : ∀ (v : ℂ) (g : ℂ → ℝ), Continuous g →
      (∀ e : ℝ, g (z + e * v) = g z - e) → (∀ w ∈ polygon n, 0 ≤ g w) → 0 < g z := by
    intro v g _ hg hP
    let p : ℝ → ℂ := fun e => z + e * v
    have hp : Continuous p := by fun_prop
    have hO : IsOpen (p ⁻¹' interior (polygon n)) := isOpen_interior.preimage hp
    have h0 : (0 : ℝ) ∈ p ⁻¹' interior (polygon n) := by simp [p, hz]
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hO 0 h0
    have hmem : p (δ / 2) ∈ interior (polygon n) := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      linarith
    have := hP _ (interior_subset hmem)
    simp only [p] at this
    rw [hg] at this
    linarith
  constructor
  · apply key (vertex n (j + 1) - vertex n j) (fx n (j + 1)) (fx_cont n (j + 1))
    · intro e
      rw [show z + (e : ℂ) * (vertex n (j + 1) - vertex n j) =
        z + (e : ℂ) * (vertex n (j + 1) - vertex n j) from rfl, fx_aff, fx_vertex hn, fx_vertex hn,
        show ((j + 1 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ) = 0 by ring,
        show ((j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ) = -1 by push_cast; ring, Xr_zero, Xr_neg_one hn]
      ring
    · intro w hw; exact (polygon_sub hn j hj hw).1
  · apply key (vertex n (j + 1) - vertex n (j + 2)) (fy n (j + 1)) (fy_cont n (j + 1))
    · intro e
      rw [fy_aff, fy_vertex hn, fy_vertex hn,
        show ((j + 1 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ) = 0 by ring,
        show ((j + 2 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ) = 1 by push_cast; ring, Yr_zero, Yr_one hn]
      ring
    · intro w hw; exact (polygon_sub hn j hj hw).2

/-- The open corner triangle lies in the interior of the polygon. -/
private lemma tri_interior (j : ℕ) {z : ℂ} (hx : 0 < fx n (j + 1) z) (hy : 0 < fy n (j + 1) z)
    (hxy : fx n (j + 1) z + fy n (j + 1) z < 1) : z ∈ interior (polygon n) := by
  have hO : IsOpen {w | 0 < fx n (j + 1) w ∧ 0 < fy n (j + 1) w ∧
      fx n (j + 1) w + fy n (j + 1) w < 1} := by
    have c1 := fx_cont n (j + 1)
    have c2 := fy_cont n (j + 1)
    refine (isOpen_lt continuous_const c1).inter ((isOpen_lt continuous_const c2).inter
      (isOpen_lt (c1.add c2) continuous_const))
  refine interior_maximal ?_ hO ⟨hx, hy, hxy⟩
  rintro w ⟨hwx, hwy, hwxy⟩
  have hn0 : 0 < n := by omega
  have hconv : Convex ℝ (polygon n) := convex_convexHull ℝ _
  have hmem := hconv.sum_mem (t := Finset.univ) (w := ![1 - fx n (j + 1) w - fy n (j + 1) w,
    fx n (j + 1) w, fy n (j + 1) w]) (z := ![vertex n (j + 1), vertex n j, vertex n (j + 2)])
    (by intro i _; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_three]; ring)
    (by intro i _; fin_cases i <;> simp <;> exact vertex_mem_polygon n _ hn0)
  rw [Fin.sum_univ_three] at hmem
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Complex.real_smul] at hmem
  convert hmem using 1
  conv_lhs => rw [recon hn j w]
  push_cast
  ring

/-- The open polygon is nonempty. -/
private lemma interior_nonempty : (interior (polygon n)).Nonempty := by
  have hs := sin_two_ph_pos hn
  have h1 := one_sub_cos_pos hn
  -- the point with frame coordinates (1/3, 1/3) at corner 1
  let z : ℂ := vertex n 1 + ((1 / 3 : ℝ) : ℂ) * (vertex n 0 - vertex n 1) +
    ((1 / 3 : ℝ) : ℂ) * (vertex n 2 - vertex n 1)
  have hx : fx n (0 + 1) z = 1 / 3 := by
    simp only [z]
    rw [show vertex n 1 + ((1 / 3 : ℝ) : ℂ) * (vertex n 0 - vertex n 1) +
      ((1 / 3 : ℝ) : ℂ) * (vertex n 2 - vertex n 1) = (vertex n 1 + ((1 / 3 : ℝ) : ℂ) *
        (vertex n 0 - vertex n 1)) + ((1 / 3 : ℝ) : ℂ) * (vertex n 2 - vertex n 1) from rfl,
      fx_aff, fx_aff, fx_vertex hn, fx_vertex hn, fx_vertex hn]
    norm_num [Xr_zero, Xr_one, Xr_neg_one hn]
  have hy : fy n (0 + 1) z = 1 / 3 := by
    simp only [z]
    rw [fy_aff, fy_aff, fy_vertex hn, fy_vertex hn, fy_vertex hn]
    norm_num [Yr_zero, Yr_one hn, Yr_neg_one]
  exact ⟨z, tri_interior hn 0 (by rw [hx]; norm_num) (by rw [hy]; norm_num)
    (by rw [hx, hy]; norm_num)⟩

end polygon

/-! ### Chords -/

/-- The parameter `t = (m+1)/(k+1)` of the internal polygon number `m+1`. -/
private noncomputable def tt (k m : ℕ) : ℝ := ((m : ℝ) + 1) / ((k : ℝ) + 1)

/-- The rational version of `tt`. -/
private def ttq (k m : ℕ) : ℚ := ((m : ℚ) + 1) / ((k : ℚ) + 1)

/-- `tt` is a rational number. -/
private lemma tt_eq_cast (k m : ℕ) : tt k m = ((ttq k m : ℚ) : ℝ) := by
  unfold tt ttq; push_cast; rfl

/-- `tt > 0`. -/
private lemma tt_pos (k m : ℕ) : 0 < tt k m := by unfold tt; positivity

/-- `tt < 1`. -/
private lemma tt_lt_one {k m : ℕ} (hm : m < k) : tt k m < 1 := by
  unfold tt
  rw [div_lt_one (by positivity)]
  have : (m : ℝ) < k := by exact_mod_cast hm
  linarith

/-- `tt` is strictly increasing. -/
private lemma tt_lt_iff (k m m' : ℕ) : tt k m < tt k m' ↔ m < m' := by
  unfold tt
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  constructor
  · intro h; exact_mod_cast (show (m : ℝ) < m' by linarith)
  · intro h; have : (m : ℝ) < m' := by exact_mod_cast h
    linarith

/-- `tt` is injective. -/
private lemma tt_inj (k m m' : ℕ) : tt k m = tt k m' ↔ m = m' := by
  constructor
  · intro h
    rcases lt_trichotomy m m' with h' | h' | h'
    · exact absurd h ((tt_lt_iff k m m').mpr h').ne
    · exact h'
    · exact absurd h ((tt_lt_iff k m' m).mpr h').ne'
  · rintro rfl; rfl

/-- The line functional of chord `(j, m)` (zero exactly on the line of the chord). -/
private noncomputable def Fl (n k j m : ℕ) (z : ℂ) : ℝ :=
  tt k m * fx n (j + 1) z + (1 - tt k m) * fy n (j + 1) z - tt k m * (1 - tt k m)

/-- Parametrisation of chord `(j, m)`: `r = 0` and `r = 1` give its endpoints. -/
private noncomputable def gam (n k j m : ℕ) (r : ℝ) : ℂ :=
  divPt n k j (m + 1) + (r : ℂ) * (divPt n k (j + 1) (m + 1) - divPt n k j (m + 1))

/-- The division points in terms of `tt`. -/
private lemma divPt_eq (n k j m : ℕ) :
    divPt n k j (m + 1) = vertex n j + (tt k m : ℂ) * (vertex n (j + 1) - vertex n j) := by
  unfold divPt tt; push_cast; ring

/-- The line functional is real-affine. -/
private lemma Fl_aff (n k j m : ℕ) (z p q : ℂ) (r : ℝ) :
    Fl n k j m (z + r * (q - p)) = Fl n k j m z + r * (Fl n k j m q - Fl n k j m p) := by
  unfold Fl; rw [fx_aff, fy_aff]; ring

/-- The line functional is continuous. -/
private lemma Fl_cont (n k j m : ℕ) : Continuous (Fl n k j m) := by
  unfold Fl
  have := fx_cont n (j + 1)
  have := fy_cont n (j + 1)
  fun_prop

/-- The "next vertex index" `j + 1` reduced modulo `n` (for `j < n`). -/
private def nx (n j : ℕ) : ℕ := if j + 1 = n then 0 else j + 1

/-- `nx n j < n`. -/
private lemma nx_lt {n j : ℕ} (hj : j < n) : nx n j < n := by unfold nx; split_ifs <;> omega

section chords
variable {n : ℕ} (hn : 3 ≤ n)
include hn

/-- Frame `x`-coordinate of a vertex at a given relative position. -/
private lemma fxv (C i : ℕ) (ρ : ℝ) (h : (i : ℝ) - (C : ℝ) = ρ) : fx n C (vertex n i) = Xr n ρ := by
  rw [fx_vertex hn, h]

/-- Frame `y`-coordinate of a vertex at a given relative position. -/
private lemma fyv (C i : ℕ) (ρ : ℝ) (h : (i : ℝ) - (C : ℝ) = ρ) : fy n C (vertex n i) = Yr n ρ := by
  rw [fy_vertex hn, h]

/-- Frame `x`-coordinate along the chord. -/
private lemma fx_gam (k j m : ℕ) (r : ℝ) : fx n (j + 1) (gam n k j m r) = (1 - tt k m) * (1 - r) := by
  unfold gam
  rw [fx_aff, divPt_eq, divPt_eq, fx_aff, fx_aff, fxv hn _ j (-1) (by push_cast; ring),
    fxv hn _ (j + 1) 0 (by push_cast; ring), fxv hn _ (j + 1 + 1) 1 (by push_cast; ring),
    Xr_neg_one hn, Xr_zero, Xr_one]
  ring

/-- Frame `y`-coordinate along the chord. -/
private lemma fy_gam (k j m : ℕ) (r : ℝ) : fy n (j + 1) (gam n k j m r) = tt k m * r := by
  unfold gam
  rw [fy_aff, divPt_eq, divPt_eq, fy_aff, fy_aff, fyv hn _ j (-1) (by push_cast; ring),
    fyv hn _ (j + 1) 0 (by push_cast; ring), fyv hn _ (j + 1 + 1) 1 (by push_cast; ring),
    Yr_neg_one, Yr_zero, Yr_one hn]
  ring

/-- The chord lies on its line. -/
private lemma Fl_gam (k j m : ℕ) (r : ℝ) : Fl n k j m (gam n k j m r) = 0 := by
  unfold Fl; rw [fx_gam hn, fy_gam hn]; ring

/-- The open chord lies in the open polygon. -/
private lemma gam_interior {k j m : ℕ} (hm : m < k) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    gam n k j m r ∈ interior (polygon n) := by
  have ht0 := tt_pos k m
  have ht1 := tt_lt_one hm
  apply tri_interior hn j
  · rw [fx_gam hn]; nlinarith
  · rw [fy_gam hn]; nlinarith
  · rw [fx_gam hn, fy_gam hn]; nlinarith

/-- The line of a chord meets the open polygon exactly in the open chord. -/
private lemma line_inter {k j m : ℕ} (hj : j < n) (hm : m < k) {z : ℂ} (hz : z ∈ interior (polygon n))
    (h0 : Fl n k j m z = 0) : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ z = gam n k j m r := by
  obtain ⟨hx, hy⟩ := interior_pos hn j hj hz
  have ht0 := tt_pos k m
  have ht1 := tt_lt_one hm
  have hlin : tt k m * fx n (j + 1) z + (1 - tt k m) * fy n (j + 1) z =
      tt k m * (1 - tt k m) := by
    unfold Fl at h0; linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = fy n (j + 1) z / tt k m := ⟨_, rfl⟩
  have hy' : fy n (j + 1) z = tt k m * r := by rw [hr]; field_simp
  have hx' : fx n (j + 1) z = (1 - tt k m) * (1 - r) := by
    have : tt k m * fx n (j + 1) z = tt k m * ((1 - tt k m) * (1 - r)) := by
      rw [hy'] at hlin; linear_combination hlin
    exact mul_left_cancel₀ ht0.ne' this
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [hr]; exact div_pos hy ht0
  · have : 0 < (1 - tt k m) * (1 - r) := hx' ▸ hx
    nlinarith
  · conv_lhs => rw [recon hn j z]
    rw [hx', hy']
    unfold gam
    rw [divPt_eq, divPt_eq]
    push_cast
    ring

omit hn in
/-- The chord as the image of `gam` on `[0, 1]`. -/
private lemma chord_eq (k : ℕ) (c : Fin n × Fin k) :
    chord n k c = gam n k c.1 c.2 '' Icc 0 1 := by
  unfold chord gam
  rw [segment_eq_image']
  ext z
  simp only [mem_image, Complex.real_smul]

/-- Inside the open polygon, a point is on a chord iff it is on its line. -/
private lemma mem_chord_iff {k : ℕ} (c : Fin n × Fin k) {z : ℂ} (hz : z ∈ interior (polygon n)) :
    z ∈ chord n k c ↔ Fl n k c.1 c.2 z = 0 := by
  rw [chord_eq]
  constructor
  · rintro ⟨r, _, rfl⟩; exact Fl_gam hn _ _ _ _
  · intro h
    obtain ⟨r, hr0, hr1, rfl⟩ := line_inter hn c.1.2 c.2.2 hz h
    exact ⟨r, ⟨hr0.le, hr1.le⟩, rfl⟩

end chords

/-! ### Meeting points of a chord with the other lines -/

/-- Value of the line functional of a chord with parameter `s` at the vertex at relative
position `ρ` from its corner. -/
private noncomputable def Fv (n : ℕ) (s ρ : ℝ) : ℝ := s * Xr n ρ + (1 - s) * Yr n ρ - s * (1 - s)

/-- Coefficient for the line at the next corner. -/
private noncomputable def aP (s t W : ℝ) : ℝ := (1 - t) * (s * W + (1 - s) ^ 2) + t * s ^ 2

/-- Coefficient for the line at the previous corner. -/
private noncomputable def bM (s t W : ℝ) : ℝ := (1 - t) * (1 - s) ^ 2 + t * (s ^ 2 + (1 - s) * W)

section pairs
variable {n : ℕ} (hn : 3 ≤ n)
include hn

/-- The line functional at a vertex. -/
private lemma Fl_vertex (k j' m' i : ℕ) :
    Fl n k j' m' (vertex n i) = Fv n (tt k m') ((i : ℝ) - ((j' + 1 : ℕ) : ℝ)) := by
  unfold Fl Fv; rw [fx_vertex hn, fy_vertex hn]

/-- The line functional of chord `(j', m')` along chord `(j, m)`. -/
private lemma Fl_gam_master (k j m j' m' : ℕ) (r : ℝ) :
    Fl n k j' m' (gam n k j m r) =
      (1 - r) * ((1 - tt k m) * Fv n (tt k m') ((j : ℝ) - (j' + 1)) +
        tt k m * Fv n (tt k m') ((j : ℝ) - j')) +
      r * ((1 - tt k m) * Fv n (tt k m') ((j : ℝ) - j') +
        tt k m * Fv n (tt k m') ((j : ℝ) + 1 - j')) := by
  unfold gam
  rw [Fl_aff, divPt_eq, divPt_eq, Fl_aff, Fl_aff, Fl_vertex hn, Fl_vertex hn, Fl_vertex hn]
  have e0 : ((j : ℕ) : ℝ) - ((j' + 1 : ℕ) : ℝ) = (j : ℝ) - (j' + 1) := by push_cast; ring
  have e1 : ((j + 1 : ℕ) : ℝ) - ((j' + 1 : ℕ) : ℝ) = (j : ℝ) - j' := by push_cast; ring
  have e2 : ((j + 1 + 1 : ℕ) : ℝ) - ((j' + 1 : ℕ) : ℝ) = (j : ℝ) + 1 - j' := by push_cast; ring
  rw [e0, e1, e2]; ring

/-- `Fv` is invariant under integer multiples of `n`. -/
private lemma Fv_shift (s ρ : ℝ) (q : ℤ) : Fv n s (ρ + q * n) = Fv n s ρ := by
  unfold Fv; rw [Xr_shift hn, Yr_shift hn]

/-- `Fv` two steps back. -/
private lemma Fv_m2 (s : ℝ) : Fv n s (-2) = s * Xr n (-2) + (1 - s) ^ 2 := by
  unfold Fv; rw [Yr_neg_two hn]; ring
/-- `Fv` one step back. -/
private lemma Fv_m1 (s : ℝ) : Fv n s (-1) = s ^ 2 := by
  unfold Fv; rw [Xr_neg_one hn, Yr_neg_one]; ring
omit hn in
/-- `Fv` at the corner. -/
private lemma Fv_0 (s : ℝ) : Fv n s 0 = -(s * (1 - s)) := by
  unfold Fv; rw [Xr_zero, Yr_zero]; ring
/-- `Fv` one step ahead. -/
private lemma Fv_1 (s : ℝ) : Fv n s 1 = (1 - s) ^ 2 := by
  unfold Fv; rw [Xr_one, Yr_one hn]; ring
/-- `Fv` two steps ahead. -/
private lemma Fv_2 (s : ℝ) : Fv n s 2 = s ^ 2 + (1 - s) * Xr n (-2) := by
  unfold Fv; rw [Xr_two hn, Yr_two_eq]; ring

/-- Every vertex other than the corner lies strictly on the far side of the line. -/
private lemma Fv_pos_int (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ρ : ℤ) (h1 : -(n : ℤ) ≤ ρ) (h2 : ρ ≤ n)
    (h0 : ρ ≠ 0) (h3 : ρ ≠ n) (h4 : ρ ≠ -n) : 0 < Fv n s ρ := by
  obtain ⟨hX, hY, hXY⟩ := XY_range hn ρ h1 h2 h0 h3 h4
  unfold Fv
  rcases le_total s (1 / 2) with h | h
  · nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hXY), mul_nonneg (sub_nonneg.mpr h) hY]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs1.le) (sub_nonneg.mpr hXY),
      mul_nonneg (sub_nonneg.mpr h) hX]

/-- Two chords at the same corner: they meet at parameter `s` along the first. -/
private lemma pair_same (k j m m' : ℕ) (r : ℝ) :
    Fl n k j m' (gam n k j m r) = (tt k m - tt k m') * (r - tt k m') := by
  rw [Fl_gam_master hn, show (j : ℝ) - (j + 1) = -1 by ring, sub_self,
    show (j : ℝ) + 1 - j = 1 by ring, Fv_m1 hn, Fv_0, Fv_1 hn]
  ring

/-- A chord and a line at the next corner. -/
private lemma pair_next (k j m m' : ℕ) (_hj : j < n) (r : ℝ) :
    Fl n k (nx n j) m' (gam n k j m r) =
      (1 - r) * aP (tt k m') (tt k m) (Xr n (-2)) + r * (tt k m' * (tt k m' - tt k m)) := by
  rw [Fl_gam_master hn]
  unfold nx
  split_ifs with h
  · have hjn : (j : ℝ) + 1 = n := by exact_mod_cast h
    rw [show (j : ℝ) - (((0 : ℕ) : ℝ) + 1) = -2 + ((1 : ℤ) : ℝ) * n by push_cast; linarith,
      show (j : ℝ) - ((0 : ℕ) : ℝ) = -1 + ((1 : ℤ) : ℝ) * n by push_cast; linarith,
      show (j : ℝ) + 1 - ((0 : ℕ) : ℝ) = 0 + ((1 : ℤ) : ℝ) * n by push_cast; linarith,
      Fv_shift hn, Fv_shift hn, Fv_shift hn, Fv_m2 hn, Fv_m1 hn, Fv_0]
    unfold aP; ring
  · rw [show (j : ℝ) - (((j + 1 : ℕ) : ℝ) + 1) = -2 by push_cast; ring,
      show (j : ℝ) - ((j + 1 : ℕ) : ℝ) = -1 by push_cast; ring,
      show (j : ℝ) + 1 - ((j + 1 : ℕ) : ℝ) = 0 by push_cast; ring, Fv_m2 hn, Fv_m1 hn, Fv_0]
    unfold aP; ring

/-- A chord and a line at the previous corner. -/
private lemma pair_prev (k j' m m' : ℕ) (_hj' : j' < n) (r : ℝ) :
    Fl n k j' m' (gam n k (nx n j') m r) =
      (1 - r) * ((1 - tt k m') * (tt k m - tt k m')) + r * bM (tt k m') (tt k m) (Xr n (-2)) := by
  rw [Fl_gam_master hn]
  unfold nx
  split_ifs with h
  · have hjn : (j' : ℝ) + 1 = n := by exact_mod_cast h
    rw [show ((0 : ℕ) : ℝ) - ((j' : ℝ) + 1) = 0 + ((-1 : ℤ) : ℝ) * n by push_cast; linarith,
      show ((0 : ℕ) : ℝ) - (j' : ℝ) = 1 + ((-1 : ℤ) : ℝ) * n by push_cast; linarith,
      show ((0 : ℕ) : ℝ) + 1 - (j' : ℝ) = 2 + ((-1 : ℤ) : ℝ) * n by push_cast; linarith,
      Fv_shift hn, Fv_shift hn, Fv_shift hn, Fv_0, Fv_1 hn, Fv_2 hn]
    unfold bM; ring
  · rw [show ((j' + 1 : ℕ) : ℝ) - ((j' : ℝ) + 1) = 0 by push_cast; ring,
      show ((j' + 1 : ℕ) : ℝ) - (j' : ℝ) = 1 by push_cast; ring,
      show ((j' + 1 : ℕ) : ℝ) + 1 - (j' : ℝ) = 2 by push_cast; ring, Fv_0, Fv_1 hn, Fv_2 hn]
    unfold bM; ring

/-- Lines at corners two or more steps away do not meet the closed chord. -/
private lemma pair_far {k j m j' m' : ℕ} (hj : j < n) (hj' : j' < n) (hm' : m' < k)
    (h1 : j' ≠ j) (h2 : j' ≠ nx n j) (h3 : j ≠ nx n j') {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hm : m < k) : 0 < Fl n k j' m' (gam n k j m r) := by
  have hs0 := tt_pos k m'
  have hs1 := tt_lt_one hm'
  have ht0 := tt_pos k m
  have ht1 := tt_lt_one hm
  unfold nx at h2 h3
  have p0 : 0 < Fv n (tt k m') ((j : ℝ) - (j' + 1)) := by
    have := Fv_pos_int hn _ hs0 hs1 ((j : ℤ) - j' - 1) (by split_ifs at * <;> omega)
      (by split_ifs at * <;> omega) (by split_ifs at * <;> omega) (by split_ifs at * <;> omega)
      (by split_ifs at * <;> omega)
    push_cast at this; convert this using 2; ring
  have p1 : 0 < Fv n (tt k m') ((j : ℝ) - j') := by
    have := Fv_pos_int hn _ hs0 hs1 ((j : ℤ) - j') (by split_ifs at * <;> omega)
      (by split_ifs at * <;> omega) (by split_ifs at * <;> omega) (by split_ifs at * <;> omega)
      (by split_ifs at * <;> omega)
    push_cast at this; exact this
  have p2 : 0 < Fv n (tt k m') ((j : ℝ) + 1 - j') := by
    have := Fv_pos_int hn _ hs0 hs1 ((j : ℤ) - j' + 1) (by split_ifs at * <;> omega)
      (by split_ifs at * <;> omega) (by split_ifs at * <;> omega) (by split_ifs at * <;> omega)
      (by split_ifs at * <;> omega)
    push_cast at this; convert this using 2; ring
  rw [Fl_gam_master hn]
  have hA : 0 < (1 - tt k m) * Fv n (tt k m') ((j : ℝ) - (j' + 1)) +
      tt k m * Fv n (tt k m') ((j : ℝ) - j') := by
    have := mul_pos (sub_pos.mpr ht1) p0; have := mul_pos ht0 p1; linarith
  have hB : 0 < (1 - tt k m) * Fv n (tt k m') ((j : ℝ) - j') +
      tt k m * Fv n (tt k m') ((j : ℝ) + 1 - j') := by
    have := mul_pos (sub_pos.mpr ht1) p1; have := mul_pos ht0 p2; linarith
  rcases eq_or_lt_of_le hr1 with h | h
  · subst h; simp [hB]
  · have := mul_pos (sub_pos.mpr h) hA
    have := mul_nonneg hr0 hB.le
    linarith

/-- `aP > 0`. -/
private lemma aP_pos {s t : ℝ} (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 < s) :
    0 < aP s t (Xr n (-2)) := by
  have hW := W_nonneg hn
  unfold aP
  have : 0 < (1 - t) * (1 - s) ^ 2 := mul_pos (by linarith) (by nlinarith)
  have : 0 ≤ (1 - t) * (s * Xr n (-2)) := mul_nonneg (by linarith) (mul_nonneg hs0.le hW)
  nlinarith

/-- `bM > 0`. -/
private lemma bM_pos {s t : ℝ} (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < bM s t (Xr n (-2)) := by
  have hW := W_nonneg hn
  unfold bM
  have : 0 < (1 - t) * (1 - s) ^ 2 := mul_pos (by linarith) (by nlinarith)
  have : 0 ≤ t * (s ^ 2 + (1 - s) * Xr n (-2)) :=
    mul_nonneg ht0.le (add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) hW))
  linarith

/-- Classification of the points where a line meets the open chord `(j, m)`. -/
private lemma cls {k j m j' m' : ℕ} (hj : j < n) (hj' : j' < n) (hm : m < k) (hm' : m' < k)
    (hne : ¬ (j' = j ∧ m' = m)) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (h : Fl n k j' m' (gam n k j m r) = 0) :
    (j' = j ∧ r = tt k m') ∨
    (j' = nx n j ∧ tt k m' < tt k m ∧
      (1 - r) * aP (tt k m') (tt k m) (Xr n (-2)) + r * (tt k m' * (tt k m' - tt k m)) = 0) ∨
    (j = nx n j' ∧ tt k m < tt k m' ∧
      (1 - r) * ((1 - tt k m') * (tt k m - tt k m')) + r * bM (tt k m') (tt k m) (Xr n (-2)) = 0) := by
  have hs0 := tt_pos k m'
  have hs1 := tt_lt_one hm'
  have ht0 := tt_pos k m
  have ht1 := tt_lt_one hm
  by_cases h1 : j' = j
  · subst h1
    left
    refine ⟨rfl, ?_⟩
    rw [pair_same hn] at h
    have hne' : tt k m - tt k m' ≠ 0 := by
      intro h'
      apply hne
      exact ⟨rfl, ((tt_inj k m' m).mp (by linarith))⟩
    have := (mul_eq_zero.mp h).resolve_left hne'
    linarith
  by_cases h2 : j' = nx n j
  · subst h2
    right; left
    rw [pair_next hn k j m m' hj] at h
    refine ⟨rfl, ?_, h⟩
    by_contra hlt
    replace hlt := not_lt.mp hlt
    have := aP_pos hn hs1 ht0 ht1 hs0
    have : 0 < (1 - r) * aP (tt k m') (tt k m) (Xr n (-2)) := mul_pos (by linarith) this
    have : 0 ≤ r * (tt k m' * (tt k m' - tt k m)) :=
      mul_nonneg hr0.le (mul_nonneg hs0.le (by linarith))
    linarith
  by_cases h3 : j = nx n j'
  · subst h3
    right; right
    rw [pair_prev hn k j' m m' hj'] at h
    refine ⟨rfl, ?_, h⟩
    by_contra hlt
    replace hlt := not_lt.mp hlt
    have := bM_pos hn hs1 ht0 ht1
    have : 0 < r * bM (tt k m') (tt k m) (Xr n (-2)) := mul_pos hr0 this
    have : 0 ≤ (1 - r) * ((1 - tt k m') * (tt k m - tt k m')) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    linarith
  exfalso
  have := pair_far hn hj hj' hm' h1 h2 h3 hr0.le hr1.le hm
  linarith

end pairs

/-! ### No three lines through one point (`n = 5`, `n ≥ 7`) -/

/-- `W = 1 + 2 cos (2π/n)` is irrational for `n = 5` and `n ≥ 7` (Niven). -/
private lemma W_irr {n : ℕ} (hn5 : n = 5 ∨ 7 ≤ n) (q : ℚ) : Xr n (-2) ≠ q := by
  have hn : 3 ≤ n := by omega
  rw [Xr_neg_two hn]
  intro h
  have hcos : Real.cos (2 * ph n) = ((q - 1) / 2 : ℚ) := by push_cast; linarith
  have hθ : ∃ r : ℚ, 2 * ph n = r * Real.pi := ⟨2 / n, by unfold ph; push_cast; ring⟩
  have hmem := niven hθ ⟨_, hcos⟩
  have hpi := Real.pi_pos
  have hnpos : (0 : ℝ) < n := n_pos hn
  have hbounds : (0 < Real.cos (2 * ph n) ∧ Real.cos (2 * ph n) < 1 / 2) ∨
      (1 / 2 < Real.cos (2 * ph n) ∧ Real.cos (2 * ph n) < 1) := by
    rcases hn5 with rfl | h7
    · left
      have e : 2 * ph 5 = 2 * Real.pi / 5 := by unfold ph; push_cast; ring
      rw [e]
      constructor
      · rw [← Real.cos_pi_div_two]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
      · rw [← Real.cos_pi_div_three]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
    · right
      have h7' : (7 : ℝ) ≤ n := by exact_mod_cast h7
      have hlt : 2 * ph n < Real.pi / 3 := by
        unfold ph
        rw [mul_div_assoc', div_lt_div_iff₀ hnpos (by norm_num)]
        nlinarith
      have hpos : 0 < 2 * ph n := by have := ph_pos hn; linarith
      constructor
      · rw [← Real.cos_pi_div_three]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) hlt
      · rw [← Real.cos_zero]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) hpos
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with e | e | e | e | e <;> rw [e] at hbounds <;> norm_num at hbounds

/-- A concurrency at the next corner would make `W` rational. -/
private lemma I1 {n : ℕ} (hn5 : n = 5 ∨ 7 ≤ n) {k a b c : ℕ} (ha : a < k) (hc : c < k)
    (h : (1 - tt k a) * aP (tt k b) (tt k c) (Xr n (-2)) + tt k a * (tt k b * (tt k b - tt k c)) = 0) :
    False := by
  have h1 := tt_lt_one ha
  have h2 := tt_lt_one hc
  have h3 := tt_pos k b
  have hα : (1 - tt k a) * (1 - tt k c) * tt k b ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) h3.ne'
  have key : Xr n (-2) = -((1 - tt k a) * ((1 - tt k c) * (1 - tt k b) ^ 2 + tt k c * tt k b ^ 2) +
      tt k a * (tt k b * (tt k b - tt k c))) / ((1 - tt k a) * (1 - tt k c) * tt k b) := by
    rw [eq_div_iff hα]; unfold aP at h; linear_combination h
  apply W_irr hn5 (-((1 - ttq k a) * ((1 - ttq k c) * (1 - ttq k b) ^ 2 + ttq k c * ttq k b ^ 2) +
    ttq k a * (ttq k b * (ttq k b - ttq k c))) / ((1 - ttq k a) * (1 - ttq k c) * ttq k b))
  rw [key]
  simp only [tt_eq_cast]
  push_cast
  ring

/-- A concurrency at the previous corner would make `W` rational. -/
private lemma I2 {n : ℕ} (hn5 : n = 5 ∨ 7 ≤ n) {k a b c : ℕ} (hb : b < k)
    (h : (1 - tt k a) * ((1 - tt k b) * (tt k c - tt k b)) + tt k a * bM (tt k b) (tt k c) (Xr n (-2)) = 0) :
    False := by
  have h1 := tt_pos k a
  have h2 := tt_lt_one hb
  have h3 := tt_pos k c
  have hα : tt k a * tt k c * (1 - tt k b) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero h1.ne' h3.ne') (by linarith)
  have key : Xr n (-2) = -((1 - tt k a) * ((1 - tt k b) * (tt k c - tt k b)) +
      tt k a * ((1 - tt k c) * (1 - tt k b) ^ 2 + tt k c * tt k b ^ 2)) /
        (tt k a * tt k c * (1 - tt k b)) := by
    rw [eq_div_iff hα]; unfold bM at h; linear_combination h
  apply W_irr hn5 (-((1 - ttq k a) * ((1 - ttq k b) * (ttq k c - ttq k b)) +
    ttq k a * ((1 - ttq k c) * (1 - ttq k b) ^ 2 + ttq k c * ttq k b ^ 2)) /
      (ttq k a * ttq k c * (1 - ttq k b)))
  rw [key]
  simp only [tt_eq_cast]
  push_cast
  ring

/-- **No triple points.** For `n = 5` and `n ≥ 7`, no point of the open polygon lies on the
lines of three distinct chords. -/
private theorem no_triple {n : ℕ} (hn5 : n = 5 ∨ 7 ≤ n) {k j₁ m₁ j₂ m₂ j₃ m₃ : ℕ}
    (hj₁ : j₁ < n) (hj₂ : j₂ < n) (hj₃ : j₃ < n) (hm₁ : m₁ < k) (hm₂ : m₂ < k) (hm₃ : m₃ < k)
    (h12 : ¬ (j₂ = j₁ ∧ m₂ = m₁)) (h13 : ¬ (j₃ = j₁ ∧ m₃ = m₁)) (h23 : ¬ (j₃ = j₂ ∧ m₃ = m₂))
    {p : ℂ} (hp : p ∈ interior (polygon n)) (e₁ : Fl n k j₁ m₁ p = 0) (e₂ : Fl n k j₂ m₂ p = 0)
    (e₃ : Fl n k j₃ m₃ p = 0) : False := by
  have hn : 3 ≤ n := by omega
  obtain ⟨r₁, hr₁0, hr₁1, hp₁⟩ := line_inter hn hj₁ hm₁ hp e₁
  obtain ⟨r₂, hr₂0, hr₂1, hp₂⟩ := line_inter hn hj₂ hm₂ hp e₂
  have c12 := cls hn hj₁ hj₂ hm₁ hm₂ h12 hr₁0 hr₁1 (hp₁ ▸ e₂)
  have c13 := cls hn hj₁ hj₃ hm₁ hm₃ h13 hr₁0 hr₁1 (hp₁ ▸ e₃)
  have c21 := cls hn hj₂ hj₁ hm₂ hm₁ (fun h => h12 ⟨h.1.symm, h.2.symm⟩) hr₂0 hr₂1 (hp₂ ▸ e₁)
  have c23 := cls hn hj₂ hj₃ hm₂ hm₃ h23 hr₂0 hr₂1 (hp₂ ▸ e₃)
  have hn5' : 5 ≤ n := by omega
  rcases c12 with ⟨a1, a2⟩ | ⟨a1, _, a3⟩ | ⟨a1, _, a3⟩ <;>
  rcases c13 with ⟨b1, b2⟩ | ⟨b1, _, b3⟩ | ⟨b1, _, b3⟩
  · exact h23 ⟨by omega, (tt_inj k m₃ m₂).mp (b2 ▸ a2)⟩
  · rw [a2] at b3; exact I1 hn5 hm₂ hm₁ b3
  · rw [a2] at b3; exact I2 hn5 hm₃ b3
  · rw [b2] at a3; exact I1 hn5 hm₃ hm₁ a3
  · -- next / next
    rcases c23 with ⟨d1, d2⟩ | ⟨d1, _, _⟩ | ⟨d1, _, _⟩
    · rcases c21 with ⟨f1, _⟩ | ⟨f1, _, _⟩ | ⟨f1, _, f3⟩
      · unfold nx at *; split_ifs at * <;> omega
      · unfold nx at *; split_ifs at * <;> omega
      · rw [d2] at f3; exact I2 hn5 hm₁ f3
    · unfold nx at *; split_ifs at * <;> omega
    · unfold nx at *; split_ifs at * <;> omega
  · -- next / prev
    rcases c23 with ⟨d1, _⟩ | ⟨d1, _, _⟩ | ⟨d1, _, _⟩ <;> (unfold nx at *; split_ifs at * <;> omega)
  · rw [b2] at a3; exact I2 hn5 hm₂ a3
  · -- prev / next
    rcases c23 with ⟨d1, _⟩ | ⟨d1, _, _⟩ | ⟨d1, _, _⟩ <;> (unfold nx at *; split_ifs at * <;> omega)
  · -- prev / prev
    rcases c23 with ⟨d1, d2⟩ | ⟨d1, _, _⟩ | ⟨d1, _, _⟩
    · rcases c21 with ⟨f1, _⟩ | ⟨f1, _, f3⟩ | ⟨f1, _, _⟩
      · unfold nx at *; split_ifs at * <;> omega
      · rw [d2] at f3; exact I1 hn5 hm₃ hm₂ f3
      · unfold nx at *; split_ifs at * <;> omega
    · unfold nx at *; split_ifs at * <;> omega
    · unfold nx at *; split_ifs at * <;> omega

/-! ### Endpoints of the chords -/

section endpoints
variable {n : ℕ} (hn : 3 ≤ n)
include hn

/-- Frame `y`-coordinate of a vertex at an integer relative position. -/
private lemma fyvi (C i : ℕ) (ρ : ℤ) (h : (i : ℤ) - C = ρ) : fy n C (vertex n i) = Yr n ρ := by
  rw [fy_vertex hn, ← h]; push_cast; ring_nf

omit hn in
/-- The division points with a general index. -/
private lemma divPt_eq' (k σ μ : ℕ) :
    divPt n k σ μ = vertex n σ +
      (((μ : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ) * (vertex n (σ + 1) - vertex n σ) := by
  unfold divPt; push_cast; ring

/-- Distinct division points are distinct points of the plane. -/
private lemma divPt_inj {k σ σ' μ μ' : ℕ} (hσ : σ < n) (hσ' : σ' < n) (hμ1 : 1 ≤ μ') (hμ2 : μ' ≤ k)
    (h : divPt n k σ μ = divPt n k σ' μ') : σ = σ' ∧ μ = μ' := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hτ0 : 0 < (μ' : ℝ) / ((k : ℝ) + 1) :=
    div_pos (by exact_mod_cast (show 0 < μ' by omega)) hk
  have hτ1 : (μ' : ℝ) / ((k : ℝ) + 1) < 1 := by
    rw [div_lt_one hk]; have : (μ' : ℝ) ≤ k := by exact_mod_cast hμ2
    linarith
  have hfy : fy n (σ + 1) (divPt n k σ μ) = 0 := by
    rw [divPt_eq', fy_aff, fyv hn _ σ (-1) (by push_cast; ring),
      fyv hn _ (σ + 1) 0 (by push_cast; ring), Yr_neg_one, Yr_zero]
    ring
  have hσeq : σ = σ' := by
    by_contra hne
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℤ, ρ = (σ' : ℤ) - σ := ⟨_, rfl⟩
    have e : fy n (σ + 1) (divPt n k σ' μ') =
        (1 - (μ' : ℝ) / ((k : ℝ) + 1)) * Yr n ((ρ - 1 : ℤ) : ℝ) +
          (μ' : ℝ) / ((k : ℝ) + 1) * Yr n (ρ : ℝ) := by
      rw [divPt_eq', fy_aff, fyvi hn _ σ' (ρ - 1) (by push_cast; omega),
        fyvi hn _ (σ' + 1) ρ (by push_cast; omega)]
      ring
    have hY0 := (XY_nonneg hn (ρ - 1) (by omega) (by omega)).2
    have hY1 := (XY_nonneg hn ρ (by omega) (by omega)).2
    have hpos : 0 < (1 - (μ' : ℝ) / ((k : ℝ) + 1)) * Yr n ((ρ - 1 : ℤ) : ℝ) +
        (μ' : ℝ) / ((k : ℝ) + 1) * Yr n (ρ : ℝ) := by
      by_cases hc : ρ = -1 ∨ ρ = n - 1
      · have := Y_pos_range hn (ρ - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        nlinarith [mul_pos (sub_pos.mpr hτ1) this, mul_nonneg hτ0.le hY1]
      · have := Y_pos_range hn ρ (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        nlinarith [mul_nonneg (sub_pos.mpr hτ1).le hY0, mul_pos hτ0 this]
    rw [← e, ← h, hfy] at hpos
    exact lt_irrefl _ hpos
  subst hσeq
  refine ⟨rfl, ?_⟩
  have hfx : ∀ μ'' : ℕ, fx n (σ + 1) (divPt n k σ μ'') = 1 - (μ'' : ℝ) / ((k : ℝ) + 1) := by
    intro μ''
    rw [divPt_eq', fx_aff, fxv hn _ σ (-1) (by push_cast; ring),
      fxv hn _ (σ + 1) 0 (by push_cast; ring), Xr_neg_one hn, Xr_zero]
    ring
  have h1 := congrArg (fx n (σ + 1)) h
  rw [hfx, hfx] at h1
  have h2 : (μ : ℝ) / ((k : ℝ) + 1) = (μ' : ℝ) / ((k : ℝ) + 1) := by linarith
  rw [div_left_inj' hk.ne'] at h2
  exact_mod_cast h2

/-- Division points on side `n` are those on side `0`. -/
private lemma divPt_succ_nx {k j μ : ℕ} (_hj : j < n) : divPt n k (j + 1) μ = divPt n k (nx n j) μ := by
  unfold nx
  split_ifs with h
  · have h0 : vertex n n = vertex n 0 := by simpa using vertex_add_n n 0 (by omega)
    have h1 : vertex n (n + 1) = vertex n (0 + 1) := by
      rw [show n + 1 = 1 + n by ring, vertex_add_n n 1 (by omega)]
    unfold divPt
    rw [h, h0, h1]
  · rfl

end endpoints

/-! ### The conjecture about non-simple intersections -/

/-- For `n = 5` and `n ≥ 7` there is never a point on three of the drawn sides. -/
private theorem no_nonsimple {n : ℕ} (hn5 : n = 5 ∨ 7 ≤ n) (k : ℕ) : ¬ HasNonSimpleIntersection n k := by
  have hn : 3 ≤ n := by omega
  rintro ⟨p, c₁, c₂, c₃, h12, h13, h23, hp1, hp2, hp3⟩
  have d : ∀ c c' : Fin n × Fin k, c ≠ c' → ¬ ((c'.1 : ℕ) = c.1 ∧ (c'.2 : ℕ) = c.2) := by
    intro c c' hcc' h
    exact hcc' (Prod.ext (Fin.ext h.1.symm) (Fin.ext h.2.symm))
  have D12 := d _ _ h12
  have D13 := d _ _ h13
  have D23 := d _ _ h23
  by_cases hpi : p ∈ interior (polygon n)
  · rw [mem_chord_iff hn _ hpi] at hp1 hp2 hp3
    exact no_triple hn5 c₁.1.2 c₂.1.2 c₃.1.2 c₁.2.2 c₂.2.2 c₃.2.2 D12 D13 D23 hpi hp1 hp2 hp3
  · have endpt : ∀ c : Fin n × Fin k, p ∈ chord n k c →
        p = divPt n k c.1 ((c.2 : ℕ) + 1) ∨ p = divPt n k (nx n c.1) ((c.2 : ℕ) + 1) := by
      intro c hc
      rw [chord_eq] at hc
      obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := hc
      rcases eq_or_lt_of_le hr0 with rfl | hr0'
      · left; simp [gam]
      rcases eq_or_lt_of_le hr1 with rfl | hr1'
      · right; simp only [gam]; rw [← divPt_succ_nx hn c.1.2]; push_cast; ring
      exact absurd (gam_interior hn c.2.2 hr0' hr1') hpi
    have key : ∀ (σ σ' : ℕ) (c c' : Fin n × Fin k), σ < n → σ' < n →
        divPt n k σ ((c.2 : ℕ) + 1) = divPt n k σ' ((c'.2 : ℕ) + 1) → σ = σ' ∧ (c.2 : ℕ) = c'.2 := by
      intro σ σ' c c' hσ hσ' h
      obtain ⟨h1, h2⟩ := divPt_inj hn hσ hσ' (by omega) (by have := c'.2.2; omega) h
      exact ⟨h1, by omega⟩
    have b1 := c₁.1.2
    have b2 := c₂.1.2
    have b3 := c₃.1.2
    have n1 := nx_lt c₁.1.2
    have n2 := nx_lt c₂.1.2
    have n3 := nx_lt c₃.1.2
    rcases endpt c₁ hp1 with e1 | e1 <;> rcases endpt c₂ hp2 with e2 | e2 <;>
      rcases endpt c₃ hp3 with e3 | e3 <;>
    · obtain ⟨s12, u12⟩ := key _ _ c₁ c₂ (by assumption) (by assumption) (e1.symm.trans e2)
      obtain ⟨s13, u13⟩ := key _ _ c₁ c₃ (by assumption) (by assumption) (e1.symm.trans e3)
      clear e1 e2 e3 endpt key d hp1 hp2 hp3
      simp only [nx] at s12 s13 n1 n2 n3
      (try split_ifs at s12 s13) <;> omega

/-- `W = 0` for the triangle. -/
private lemma W3 : Xr 3 (-2) = 0 := by
  rw [Xr_neg_two (by norm_num)]
  have : 2 * ph 3 = Real.pi - Real.pi / 3 := by unfold ph; push_cast; ring
  rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num

/-- `W = 1` for the square. -/
private lemma W4 : Xr 4 (-2) = 1 := by
  rw [Xr_neg_two (by norm_num)]
  have : 2 * ph 4 = Real.pi / 2 := by unfold ph; push_cast; ring
  rw [this, Real.cos_pi_div_two]; norm_num

/-- `W = 2` for the hexagon. -/
private lemma W6 : Xr 6 (-2) = 2 := by
  rw [Xr_neg_two (by norm_num)]
  have : 2 * ph 6 = Real.pi / 3 := by unfold ph; push_cast; ring
  rw [this, Real.cos_pi_div_three]; norm_num

/-- A triple point from chords `(0, m₁)`, `(0, m₂)` and `(1, m₃)`. -/
private lemma triple_exists {n k m₁ m₂ m₃ : ℕ} (hn : 3 ≤ n) (h1 : m₁ < k) (h2 : m₂ < k) (h3 : m₃ < k)
    (hne : m₁ ≠ m₂)
    (heq : (1 - tt k m₂) * aP (tt k m₃) (tt k m₁) (Xr n (-2)) +
      tt k m₂ * (tt k m₃ * (tt k m₃ - tt k m₁)) = 0) :
    HasNonSimpleIntersection n k := by
  have hpi : gam n k 0 m₁ (tt k m₂) ∈ interior (polygon n) :=
    gam_interior hn h1 (tt_pos k m₂) (tt_lt_one h2)
  let c₁ : Fin n × Fin k := (⟨0, by omega⟩, ⟨m₁, h1⟩)
  let c₂ : Fin n × Fin k := (⟨0, by omega⟩, ⟨m₂, h2⟩)
  let c₃ : Fin n × Fin k := (⟨1, by omega⟩, ⟨m₃, h3⟩)
  refine ⟨gam n k 0 m₁ (tt k m₂), c₁, c₂, c₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply hne; have := congrArg (fun c => (c.2 : ℕ)) h; simpa [c₁, c₂] using this
  · intro h; have := congrArg (fun c => (c.1 : ℕ)) h; simp [c₁, c₃] at this
  · intro h; have := congrArg (fun c => (c.1 : ℕ)) h; simp [c₂, c₃] at this
  · rw [chord_eq]; exact ⟨tt k m₂, ⟨(tt_pos k m₂).le, (tt_lt_one h2).le⟩, rfl⟩
  · rw [mem_chord_iff hn _ hpi]; show Fl n k 0 m₂ (gam n k 0 m₁ (tt k m₂)) = 0
    rw [pair_same hn]; ring
  · rw [mem_chord_iff hn _ hpi]
    show Fl n k 1 m₃ (gam n k 0 m₁ (tt k m₂)) = 0
    have hnx : nx n 0 = 1 := by unfold nx; split_ifs <;> omega
    have := pair_next hn k 0 m₁ m₃ (by omega) (tt k m₂)
    rw [hnx] at this
    rw [this]; exact heq

/-- A triple point for the triangle (`k = 5`). -/
private lemma triple3 : HasNonSimpleIntersection 3 5 :=
  triple_exists (m₁ := 2) (m₂ := 4) (m₃ := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [W3]; unfold aP tt; norm_num)

/-- A triple point for the square (`k = 5`). -/
private lemma triple4 : HasNonSimpleIntersection 4 5 :=
  triple_exists (m₁ := 3) (m₂ := 4) (m₃ := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [W4]; unfold aP tt; norm_num)

/-- A triple point for the hexagon (`k = 9`). -/
private lemma triple6 : HasNonSimpleIntersection 6 9 :=
  triple_exists (m₁ := 4) (m₂ := 8) (m₃ := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [W6]; unfold aP tt; norm_num)

/-! ### Counting the regions -/

/-- The line functionals, indexed by `i = n m + j`. -/
private noncomputable def fL (n k i : ℕ) (z : ℂ) : ℝ := Fl n k (i % n) (i / n) z

/-- The region set is the complement of the `n k` lines in the open polygon. -/
private lemma regionSet_eq {n : ℕ} (hn : 3 ≤ n) (k : ℕ) :
    regionSet n k = cellSet (interior (polygon n)) (fL n k) (n * k) := by
  ext z
  simp only [regionSet, cellSet, mem_sdiff, mem_iUnion, not_exists, mem_ofPred_eq, fL]
  constructor
  · rintro ⟨hz, hno⟩
    refine ⟨hz, fun i hi h0 => ?_⟩
    have hj : i % n < n := Nat.mod_lt _ (by omega)
    have hm : i / n < k := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [mul_comm] at hi; exact hi
    apply hno (⟨i % n, hj⟩, ⟨i / n, hm⟩)
    rw [mem_chord_iff hn _ hz]
    exact h0
  · rintro ⟨hz, hno⟩
    refine ⟨hz, fun c hc => ?_⟩
    rw [mem_chord_iff hn _ hz] at hc
    have hi : n * (c.2 : ℕ) + c.1 < n * k := by
      have h1 := c.1.2
      have h2 : n * ((c.2 : ℕ) + 1) ≤ n * k := Nat.mul_le_mul_left _ c.2.2
      rw [Nat.mul_succ] at h2
      omega
    apply hno _ hi
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt c.1.2, Nat.mul_add_div (by omega),
      Nat.div_eq_of_lt c.1.2, add_zero]
    exact hc

/-- `nx n j ≠ j`. -/
private lemma nx_ne {n j : ℕ} (hn : 3 ≤ n) (_hj : j < n) : nx n j ≠ j := by
  unfold nx; split_ifs <;> omega

/-- The number of distinct points of the open chord `(j, m)` on earlier lines is `2m`. -/
private lemma roots_count {n k j m : ℕ} (hn5 : n = 5 ∨ 7 ≤ n) (hj : j < n) (hm : m < k) :
    {r : ℝ | 0 < r ∧ r < 1 ∧ ∃ i' < n * m + j, fL n k i' (gam n k j m r) = 0}.ncard = 2 * m := by
  have hn : 3 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have ht0 := tt_pos k m
  have ht1 := tt_lt_one hm
  let ρP : ℕ → ℝ := fun m' => aP (tt k m') (tt k m) (Xr n (-2)) /
    (aP (tt k m') (tt k m) (Xr n (-2)) + tt k m' * (tt k m - tt k m'))
  have hρP : ∀ m' < m, 0 < ρP m' ∧ ρP m' < 1 ∧
      Fl n k (nx n j) m' (gam n k j m (ρP m')) = 0 := by
    intro m' hm'
    have hs0 := tt_pos k m'
    have hs1 := tt_lt_one (show m' < k by omega)
    have hst := (tt_lt_iff k m' m).mpr hm'
    have ha := aP_pos hn hs1 ht0 ht1 hs0
    have hb : 0 < tt k m' * (tt k m - tt k m') := mul_pos hs0 (by linarith)
    refine ⟨div_pos ha (by linarith), (div_lt_one (by linarith)).mpr (by linarith), ?_⟩
    rw [pair_next hn k j m m' hj]
    simp only [ρP]
    field_simp
    ring
  have hset : {r : ℝ | 0 < r ∧ r < 1 ∧ ∃ i' < n * m + j, fL n k i' (gam n k j m r) = 0} =
      (tt k '' Iio m) ∪ (ρP '' Iio m) := by
    ext r
    simp only [mem_ofPred_eq, mem_union, mem_image, mem_Iio, fL]
    constructor
    · rintro ⟨hr0, hr1, i', hi', h0⟩
      have hj' : i' % n < n := Nat.mod_lt _ hn0
      have hdm := Nat.div_add_mod i' n
      have hm'le : i' / n ≤ m := by
        have : i' / n ≤ (n * m + j) / n := Nat.div_le_div_right hi'.le
        rwa [Nat.mul_add_div hn0, Nat.div_eq_of_lt hj, add_zero] at this
      have hm'k : i' / n < k := by omega
      have hne : ¬ (i' % n = j ∧ i' / n = m) := by
        rintro ⟨h1, h2⟩
        rw [h1, h2] at hdm
        omega
      rcases cls hn hj hj' hm hm'k hne hr0 hr1 h0 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · left
        refine ⟨i' / n, ?_, h2.symm⟩
        rcases eq_or_lt_of_le hm'le with h | h
        · exact absurd ⟨h1, h⟩ hne
        · exact h
      · right
        have hlt := (tt_lt_iff k _ m).mp h2
        refine ⟨i' / n, hlt, ?_⟩
        have hs0 := tt_pos k (i' / n)
        have hs1 := tt_lt_one hm'k
        have ha := aP_pos hn hs1 ht0 ht1 hs0
        have hb : 0 < tt k (i' / n) * (tt k m - tt k (i' / n)) := mul_pos hs0 (by linarith)
        simp only [ρP]
        rw [div_eq_iff (by linarith)]
        linear_combination h3
      · exfalso
        have := (tt_lt_iff k m _).mp h2
        omega
    · rintro (⟨m', hm', rfl⟩ | ⟨m', hm', rfl⟩)
      · refine ⟨tt_pos k m', tt_lt_one (by omega), n * m' + j, ?_, ?_⟩
        · have h2 : n * (m' + 1) ≤ n * m := Nat.mul_le_mul_left _ hm'
          rw [Nat.mul_succ] at h2
          omega
        · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj, Nat.mul_add_div hn0, Nat.div_eq_of_lt hj,
            add_zero, pair_same hn]
          ring
      · obtain ⟨h0, h1, h2⟩ := hρP m' hm'
        refine ⟨h0, h1, n * m' + nx n j, ?_, ?_⟩
        · have := nx_lt hj
          have h3 : n * (m' + 1) ≤ n * m := Nat.mul_le_mul_left _ hm'
          rw [Nat.mul_succ] at h3
          omega
        · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (nx_lt hj), Nat.mul_add_div hn0,
            Nat.div_eq_of_lt (nx_lt hj), add_zero]
          exact h2
  have hinj1 : InjOn (tt k) (Iio m) := fun a _ b _ h => (tt_inj k a b).mp h
  have hinj2 : InjOn ρP (Iio m) := by
    intro a ha b hb hab
    by_contra hne
    simp only [mem_Iio] at ha hb
    obtain ⟨h0, h1, e2⟩ := hρP a ha
    obtain ⟨_, _, e3⟩ := hρP b hb
    rw [← hab] at e3
    exact no_triple hn5 hj (nx_lt hj) (nx_lt hj) hm (show a < k by omega) (show b < k by omega)
      (fun h => nx_ne hn hj h.1) (fun h => nx_ne hn hj h.1) (fun h => hne h.2.symm)
      (gam_interior hn hm h0 h1) (Fl_gam hn k j m _) e2 e3
  have hdisj : Disjoint (tt k '' Iio m) (ρP '' Iio m) := by
    rw [Set.disjoint_left]
    rintro r ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    simp only [mem_Iio] at ha hb
    obtain ⟨_, _, e3⟩ := hρP b hb
    rw [hab] at e3
    have e2 : Fl n k j a (gam n k j m (tt k a)) = 0 := by rw [pair_same hn]; ring
    exact no_triple hn5 hj hj (nx_lt hj) hm (show a < k by omega) (show b < k by omega)
      (fun h => by omega) (fun h => nx_ne hn hj h.1) (fun h => nx_ne hn hj h.1)
      (gam_interior hn hm (tt_pos k a) (tt_lt_one (by omega))) (Fl_gam hn k j m _) e2 e3
  rw [hset, Set.ncard_union_eq hdisj ((Set.finite_Iio m).image _) ((Set.finite_Iio m).image _),
    hinj1.ncard_image, hinj2.ncard_image, Set.ncard_Iio_nat]
  ring

/-- `∑_{i < nk} (1 + 2 ⌊i/n⌋) = n k²`. -/
private lemma sum_formula (n k : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.range (n * k), (1 + 2 * (i / n)) = n * k ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have : ∀ x ∈ Finset.range n, 1 + 2 * ((n * k + x) / n) = 1 + 2 * k := by
      intro x hx
      rw [Nat.mul_add_div hn, Nat.div_eq_of_lt (Finset.mem_range.mp hx), add_zero]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring

/-- **The region count.** For `n = 5` and `n ≥ 7` the `k` internal `n`-gons cut the `n`-gon
into `n k² + 1` regions. -/
private theorem regions_formula {n : ℕ} (hn5 : n = 5 ∨ 7 ≤ n) (k : ℕ) : regions n k = n * k ^ 2 + 1 := by
  have hn : 3 ≤ n := by omega
  have hn0 : 0 < n := by omega
  unfold regions
  rw [regionSet_eq hn k]
  have hU : IsOpen (interior (polygon n)) := isOpen_interior
  have hUc : Convex ℝ (interior (polygon n)) := (convex_convexHull ℝ _).interior
  have hfa : ∀ i (z w : ℂ) (r : ℝ), fL n k i (z + r * (w - z)) =
      fL n k i z + r * (fL n k i w - fL n k i z) := fun i z w r => Fl_aff _ _ _ _ z z w r
  have hfc : ∀ i, Continuous (fL n k i) := fun i => Fl_cont _ _ _ _
  rw [count_general hU hUc hfa hfc (interior_nonempty hn)
    (fun i => divPt n k (i % n) (i / n + 1)) (fun i => divPt n k (i % n + 1) (i / n + 1)) (n * k)]
  · rw [Finset.sum_congr rfl (g := fun i => 1 + 2 * (i / n)), sum_formula n k hn0]
    · ring
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hj : i % n < n := Nat.mod_lt _ hn0
    have hm : i / n < k := by rw [Nat.div_lt_iff_lt_mul hn0]; rw [mul_comm] at hi'; exact hi'
    have := roots_count hn5 hj hm
    rw [Nat.div_add_mod] at this
    rw [← this]
    rfl
  · intro i hi z hz h0
    have hj : i % n < n := Nat.mod_lt _ hn0
    have hm : i / n < k := by rw [Nat.div_lt_iff_lt_mul hn0]; rw [mul_comm] at hi; exact hi
    exact line_inter hn hj hm hz h0
  · intro i hi r hr0 hr1
    have hm : i / n < k := by rw [Nat.div_lt_iff_lt_mul hn0]; rw [mul_comm] at hi; exact hi
    exact ⟨gam_interior hn hm hr0 hr1, Fl_gam hn k _ _ r⟩
  · intro i hi
    have hm : i / n < k := by rw [Nat.div_lt_iff_lt_mul hn0]; rw [mul_comm] at hi; exact hi
    refine ⟨vertex n (i % n + 1), ?_⟩
    show Fl n k (i % n) (i / n) (vertex n (i % n + 1)) ≠ 0
    unfold Fl
    rw [fxv hn _ _ 0 (by ring), fyv hn _ _ 0 (by ring), Xr_zero, Yr_zero]
    have := tt_pos k (i / n)
    have := tt_lt_one hm
    nlinarith
  · intro i hi i' hi'
    have hj : i % n < n := Nat.mod_lt _ hn0
    have hm : i / n < k := by rw [Nat.div_lt_iff_lt_mul hn0]; rw [mul_comm] at hi; exact hi
    have hj' : i' % n < n := Nat.mod_lt _ hn0
    have hm' : i' / n < k := by
      rw [Nat.div_lt_iff_lt_mul hn0]; rw [mul_comm] at hi; exact lt_trans hi' hi
    have hne : ¬ (i' % n = i % n ∧ i' / n = i / n) := by
      rintro ⟨h1, h2⟩
      have e1 := Nat.div_add_mod i n
      have e2 := Nat.div_add_mod i' n
      rw [h1, h2] at e2
      omega
    show ∃ r : ℝ, Fl n k (i' % n) (i' / n) (gam n k (i % n) (i / n) r) ≠ 0
    have hs0 := tt_pos k (i' / n)
    have hs1 := tt_lt_one hm'
    have ht0 := tt_pos k (i / n)
    have ht1 := tt_lt_one hm
    by_cases h1 : i' % n = i % n
    · refine ⟨0, ?_⟩
      rw [h1, pair_same hn]
      have : tt k (i / n) ≠ tt k (i' / n) := fun h => hne ⟨h1, ((tt_inj k _ _).mp h).symm⟩
      have : tt k (i / n) - tt k (i' / n) ≠ 0 := sub_ne_zero.mpr this
      have : (0 : ℝ) - tt k (i' / n) ≠ 0 := by linarith
      exact mul_ne_zero (by assumption) this
    by_cases h2 : i' % n = nx n (i % n)
    · refine ⟨0, ?_⟩
      rw [h2, pair_next hn k _ _ _ hj]
      have := aP_pos hn hs1 ht0 ht1 hs0
      simp only [sub_zero, one_mul, zero_mul, add_zero]
      exact this.ne'
    by_cases h3 : i % n = nx n (i' % n)
    · refine ⟨1, ?_⟩
      rw [h3, pair_prev hn k _ _ _ hj']
      have := bM_pos hn hs1 ht0 ht1
      simp only [sub_self, zero_mul, one_mul, zero_add]
      exact this.ne'
    · refine ⟨0, ?_⟩
      exact (pair_far hn hj hj' hm' h1 h2 h3 le_rfl zero_le_one hm).ne'

/-- The conjecture of A357216: non-simple intersections occur exactly for the triangle, the
square and the hexagon, and otherwise there are `n k² + 1` regions. -/
theorem result : statement := by
  refine ⟨fun n hn => ⟨fun ⟨k, hk⟩ => ?_, fun h => ?_⟩, fun n k hn => regions_formula hn k⟩
  · by_contra hc
    exact no_nonsimple (show n = 5 ∨ 7 ≤ n by omega) k hk
  · rcases h with rfl | rfl | rfl
    · exact ⟨5, triple3⟩
    · exact ⟨5, triple4⟩
    · exact ⟨9, triple6⟩

end Math0.Frontier.A357216

#math0_settles Math0.Frontier.A357216.result Math0.Statements.A357216.statement
