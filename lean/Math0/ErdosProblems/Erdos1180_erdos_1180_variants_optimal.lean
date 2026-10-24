/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1180»
import Math0.Audit

/-!
# Erdős Problem 1180: the "optimal" variant is false as stated

Erdős Problem 1180 (Erdős–Graham) asks whether, for each `ε > 0`, every residue modulo every
prime `p` is a sum of at most `C_ε` inverses `n⁻¹` with `1 ≤ n ≤ p ^ ε`; upstream `C ε` is the
least such constant (minimum over *all* primes). The upstream variant
`erdos_1180.variants.optimal` asserts `C ε ≤ ε⁻¹ ^ (1 + δ)` for every `δ > 0` and all small
`ε > 0`. We refute it: for `ε = 1 / (m + 1)` and a Bertrand prime `2 ^ m < p < 2 ^ (m + 1)`
we have `p ^ ε < 2`, so the only admissible denominator is `1` and representing `-1` needs
`p - 1 ≥ 2 ^ m` summands; hence `C ε ≥ 2 ^ m > (m + 1) ^ 2 = ε⁻¹ ^ 2`. This lower bound needs
the defining set of `C ε` to be nonempty, i.e. the (true) main statement `erdos_1180`, which we
prove following Glibichuk (2006): sums of reciprocals of primes in `k` disjoint blocks give an
antisymmetric set `B` with `|B|² > p`, Glibichuk's covering lemma (via an energy argument and
Cauchy–Davenport) gives `8 · B · B = ZMod p`, and each element of `B · B` is a sum of `k²`
inverses of products of two small primes. This formalization of Glibichuk's argument is adapted
(lists replaced by multisets, upstream `Represents` used directly) from the Apache-2.0 proof in
`plby/lean-proofs` (`ErdosProblems/Erdos1180.lean`).
-/

open scoped Pointwise
open Finset

namespace Math0.Erdos1180

/- Glibichuk covering lemma -/

section Glibichuk

variable {p : ℕ} [NeZero p]

/-- The image of `X × Y` under `(x, y) ↦ x + ξ y`. -/
noncomputable def affImg (ξ : ZMod p) (X Y : Finset (ZMod p)) : Finset (ZMod p) :=
  (X ×ˢ Y).image fun z ↦ z.1 + ξ * z.2

/-- The number of pairs of points of `X × Y` with the same image under `(x, y) ↦ x + ξ y`. -/
noncomputable def affEnergy (ξ : ZMod p) (X Y : Finset (ZMod p)) : ℕ :=
  #{z ∈ (X ×ˢ Y) ×ˢ (X ×ˢ Y) | z.1.1 + ξ * z.1.2 = z.2.1 + ξ * z.2.2}

omit [NeZero p] in
/-- The energy is the sum of the squares of the fibre sizes. -/
lemma affEnergy_eq_sum_sq (ξ : ZMod p) (X Y : Finset (ZMod p)) :
    affEnergy ξ X Y = ∑ a ∈ affImg ξ X Y, #{z ∈ X ×ˢ Y | z.1 + ξ * z.2 = a} ^ 2 := by
  classical
  simp_rw [affEnergy, sq, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop (add simp [affImg])

omit [NeZero p] in
/-- Cauchy–Schwarz: `(|X||Y|)² ≤ |X + ξY| · E_ξ(X, Y)`. -/
lemma card_sq_le_card_affImg_mul_energy (ξ : ZMod p) (X Y : Finset (ZMod p)) :
    (#X * #Y) ^ 2 ≤ #(affImg ξ X Y) * affEnergy ξ X Y := by
  classical
  let D := X ×ˢ Y
  let f : ZMod p × ZMod p → ZMod p := fun z ↦ z.1 + ξ * z.2
  calc
    (#X * #Y) ^ 2 = (∑ a ∈ affImg ξ X Y, #{z ∈ D | f z = a}) ^ 2 := by
      rw [← card_product]
      congr 1
      rw [sum_card_fiberwise_eq_card_filter, filter_eq_self.2]
      intro z hz
      exact mem_image.mpr ⟨z, hz, rfl⟩
    _ ≤ #(affImg ξ X Y) * ∑ a ∈ affImg ξ X Y, #{z ∈ D | f z = a} ^ 2 := by
      simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ)
        (affImg ξ X Y) 1 (fun a ↦ #{z ∈ D | f z = a})
    _ = #(affImg ξ X Y) * affEnergy ξ X Y := by
      rw [affEnergy_eq_sum_sq]

/-- The nonzero residues. -/
noncomputable def units' (p : ℕ) [NeZero p] : Finset (ZMod p) := univ.erase 0

/-- There are `p - 1` nonzero residues. -/
@[simp] lemma card_units' : #(units' p) = p - 1 := by
  classical
  rw [units', card_erase_of_mem (mem_univ 0), card_univ, ZMod.card]

/-- Double counting a filtered product. -/
lemma sum_card_filter_eq {α β : Type*}
    (s : Finset α) (t : Finset β) (P : α → β → Prop) [DecidableRel P] :
    ∑ a ∈ s, #(t.filter (P a)) = #((s ×ˢ t).filter fun z ↦ P z.1 z.2) := by
  classical
  rw [card_filter, sum_product]
  apply sum_congr rfl
  intro a _
  rw [card_filter]

/-- The total energy over all nonzero slopes, as one count. -/
lemma sum_affEnergy_eq_card (X Y : Finset (ZMod p)) :
    ∑ ξ ∈ units' p, affEnergy ξ X Y =
      #{w ∈ units' p ×ˢ ((X ×ˢ Y) ×ˢ (X ×ˢ Y)) |
        w.2.1.1 + w.1 * w.2.1.2 = w.2.2.1 + w.1 * w.2.2.2} := by
  classical
  unfold affEnergy
  exact sum_card_filter_eq (units' p) ((X ×ˢ Y) ×ˢ (X ×ˢ Y))
    (fun ξ (w : (ZMod p × ZMod p) × (ZMod p × ZMod p)) ↦
      w.1.1 + ξ * w.1.2 = w.2.1 + ξ * w.2.2)

omit [NeZero p] in
/-- Two distinct points determine at most one slope under which they collide. -/
lemma slope_unique (hp : p.Prime) {ξ η : ZMod p}
    {u v : ZMod p × ZMod p} (huv : u ≠ v)
    (hξ : u.1 + ξ * u.2 = v.1 + ξ * v.2)
    (hη : u.1 + η * u.2 = v.1 + η * v.2) : ξ = η := by
  have := Fact.mk hp
  have hy : u.2 ≠ v.2 := by
    intro hy
    apply huv
    apply Prod.ext
    · rw [hy] at hξ
      exact add_right_cancel hξ
    · exact hy
  have hmul : (ξ - η) * (u.2 - v.2) = 0 := by
    linear_combination hξ - hη
  rcases mul_eq_zero.mp hmul with h | h
  · exact sub_eq_zero.mp h
  · exact (hy (sub_eq_zero.mp h)).elim

/-- `∑_{ξ ≠ 0} E_ξ(X, Y) ≤ (p - 1)|X||Y| + (|X||Y|)²`. -/
lemma sum_affEnergy_le (hp : p.Prime) (X Y : Finset (ZMod p)) :
    ∑ ξ ∈ units' p, affEnergy ξ X Y ≤ #(units' p) * (#X * #Y) + (#X * #Y) ^ 2 := by
  classical
  let D := X ×ˢ Y
  let U := units' p ×ˢ (D ×ˢ D)
  let C := U.filter fun w ↦ w.2.1.1 + w.1 * w.2.1.2 = w.2.2.1 + w.1 * w.2.2.2
  let Cd := C.filter fun w ↦ w.2.1 = w.2.2
  let Co := C.filter fun w ↦ w.2.1 ≠ w.2.2
  have hsum : ∑ ξ ∈ units' p, affEnergy ξ X Y = #C := by
    simpa [C, U, D] using sum_affEnergy_eq_card (p := p) X Y
  have hsplit : #Cd + #Co = #C := by
    simpa [Cd, Co] using card_filter_add_card_filter_not (s := C) (fun w ↦ w.2.1 = w.2.2)
  have hdiag : #Cd ≤ #(units' p ×ˢ D) := by
    refine card_le_card_of_injOn (fun w ↦ (w.1, w.2.1)) ?_ ?_
    · intro w hw
      simp only [Cd, C, U, mem_filter, coe_filter, Set.mem_ofPred_eq, mem_product] at hw
      exact mem_product.mpr ⟨hw.1.1.1, hw.1.1.2.1⟩
    · intro w hw w' hw' heq
      simp only [Cd, C, U, coe_filter, Set.mem_ofPred_eq, mem_filter] at hw hw'
      have hξ : w.1 = w'.1 := congrArg (fun z ↦ z.1) heq
      have hu : w.2.1 = w'.2.1 := congrArg (fun z ↦ z.2) heq
      have hv : w.2.2 = w'.2.2 := by rw [← hw.2, hu, hw'.2]
      exact Prod.ext hξ (Prod.ext hu hv)
  have hoff : #Co ≤ #(D ×ˢ D) := by
    refine card_le_card_of_injOn (fun w ↦ w.2) ?_ ?_
    · intro w hw
      simp only [Co, C, U, mem_filter, coe_filter, Set.mem_ofPred_eq, mem_product] at hw
      exact mem_product.mpr hw.1.1.2
    · intro w hw w' hw' heq
      simp only [Co, C, U, coe_filter, Set.mem_ofPred_eq, mem_filter] at hw hw'
      have hξ : w.1 = w'.1 := by
        apply slope_unique hp hw.2 hw.1.2
        simpa [heq] using hw'.1.2
      exact Prod.ext hξ heq
  rw [hsum, ← hsplit]
  calc
    #Cd + #Co ≤ #(units' p ×ˢ D) + #(D ×ˢ D) := Nat.add_le_add hdiag hoff
    _ = #(units' p) * (#X * #Y) + (#X * #Y) ^ 2 := by simp [D, pow_two]

/-- Some nonzero slope has energy at most the average. -/
lemma exists_good_slope (hp : p.Prime) (X Y : Finset (ZMod p)) :
    ∃ ξ ∈ units' p,
      (affEnergy ξ X Y : ℚ) ≤ (#X * #Y : ℚ) + (#X * #Y : ℚ) ^ 2 / #(units' p) := by
  classical
  have hGpos : 0 < #(units' p) := by
    rw [card_units']
    exact Nat.sub_pos_of_lt hp.one_lt
  have hnat := sum_affEnergy_le (p := p) hp X Y
  have hcast : (∑ ξ ∈ units' p, (affEnergy ξ X Y : ℚ)) ≤
      (#(units' p) : ℚ) * (#X * #Y : ℚ) + (#X * #Y : ℚ) ^ 2 := by
    exact_mod_cast hnat
  have hsum : (∑ ξ ∈ units' p, (affEnergy ξ X Y : ℚ)) ≤
      ∑ ξ ∈ units' p, ((#X * #Y : ℚ) + (#X * #Y : ℚ) ^ 2 / #(units' p)) := by
    refine hcast.trans (le_of_eq ?_)
    simp only [sum_const, nsmul_eq_mul]
    field_simp [Nat.ne_of_gt hGpos]
  exact exists_le_of_sum_le (card_pos.mp hGpos) hsum

omit [NeZero p] in
/-- Replacing `ξ` by `-ξ` does not change the energy (swap the `Y`-coordinates). -/
lemma affEnergy_neg (ξ : ZMod p) (X Y : Finset (ZMod p)) :
    affEnergy (-ξ) X Y = affEnergy ξ X Y := by
  classical
  let sw : ((ZMod p × ZMod p) × (ZMod p × ZMod p)) →
      ((ZMod p × ZMod p) × (ZMod p × ZMod p)) := fun w ↦ ((w.1.1, w.2.2), (w.2.1, w.1.2))
  have hinv : Function.Involutive sw := by
    rintro ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
    rfl
  unfold affEnergy
  apply card_bijective sw hinv.bijective
  rintro ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
  simp only [mem_filter, mem_product]
  constructor
  · rintro ⟨⟨⟨hx₁, hy₁⟩, ⟨hx₂, hy₂⟩⟩, h⟩
    refine ⟨⟨⟨hx₁, hy₂⟩, ⟨hx₂, hy₁⟩⟩, ?_⟩
    dsimp [sw]
    linear_combination h
  · rintro ⟨⟨⟨hx₁, hy₂⟩, ⟨hx₂, hy₁⟩⟩, h⟩
    refine ⟨⟨⟨hx₁, hy₁⟩, ⟨hx₂, hy₂⟩⟩, ?_⟩
    dsimp [sw] at h
    linear_combination h

/-- If `|X||Y| > p` and the slope `ξ` has small energy then `|X + ξY| > p / 2`. -/
lemma card_affImg_large (hp : p.Prime) (hp2 : 2 < p)
    (X Y : Finset (ZMod p)) (ξ : ZMod p) (hprod : p < #X * #Y)
    (henergy : (affEnergy ξ X Y : ℚ) ≤ (#X * #Y : ℚ) + (#X * #Y : ℚ) ^ 2 / #(units' p)) :
    p < 2 * #(affImg ξ X Y) := by
  classical
  let q : ℚ := #X * #Y
  let s : ℚ := #(affImg ξ X Y)
  let e : ℚ := affEnergy ξ X Y
  let r : ℚ := ((p - 1 : ℕ) : ℚ)
  rw [card_units'] at henergy
  have hrposN : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hrpos : (0 : ℚ) < r := by
    dsimp [r]
    exact_mod_cast hrposN
  have hrEq : r = (p : ℚ) - 1 := by
    dsimp [r]
    rw [Nat.cast_sub hp.one_lt.le]
    norm_num
  have hqpos : (0 : ℚ) < q := by
    dsimp [q]
    exact_mod_cast (lt_trans hp.pos hprod)
  have hpq : (p : ℚ) < q := by
    dsimp [q]
    exact_mod_cast hprod
  have hcauchy : q ^ 2 ≤ s * e := by
    dsimp [q, s, e]
    exact_mod_cast card_sq_le_card_affImg_mul_energy (p := p) ξ X Y
  by_contra hlarge
  have hsNat : 2 * #(affImg ξ X Y) ≤ p := Nat.le_of_not_gt hlarge
  have hpodd : ¬ Even p := by
    rw [hp.even_iff]
    omega
  have hslt : 2 * #(affImg ξ X Y) < p := by
    apply lt_of_le_of_ne hsNat
    intro heq
    exact hpodd ⟨#(affImg ξ X Y), by omega⟩
  have hs : 2 * s ≤ r := by
    dsimp [s, r]
    exact_mod_cast (show 2 * #(affImg ξ X Y) ≤ p - 1 by omega)
  have he0 : 0 ≤ e := by positivity
  have hc2 : 2 * q ^ 2 ≤ r * e := by
    have h₁ := mul_le_mul_of_nonneg_left hcauchy (show (0 : ℚ) ≤ 2 by norm_num)
    have h₂ := mul_le_mul_of_nonneg_right hs he0
    nlinarith
  have hemul : e * r ≤ q * r + q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right henergy (le_of_lt hrpos)
    dsimp [q, e, r] at h ⊢
    field_simp [ne_of_gt hrpos] at h
    simpa [pow_two, mul_add, mul_comm, mul_left_comm, mul_assoc] using h
  nlinarith [hrEq]

/-- There is a nonzero `ξ` such that both `X + ξY` and `X - ξY` have more than `p / 2`
elements. -/
lemma exists_two_large_affImg (hp : p.Prime) (hp2 : 2 < p)
    (X Y : Finset (ZMod p)) (hprod : p < #X * #Y) :
    ∃ ξ ∈ units' p, p < 2 * #(affImg ξ X Y) ∧ p < 2 * #(affImg (-ξ) X Y) := by
  obtain ⟨ξ, hξ, henergy⟩ := exists_good_slope (p := p) hp X Y
  refine ⟨ξ, hξ, card_affImg_large hp hp2 X Y ξ hprod henergy, ?_⟩
  apply card_affImg_large hp hp2 X Y (-ξ) hprod
  simpa [affEnergy_neg] using henergy

/-- `Y` contains no pair `y, -y`. -/
def Antisymm (Y : Finset (ZMod p)) : Prop :=
  ∀ y ∈ Y, -y ∉ Y

/-- `XY + XY + XY + XY`. -/
noncomputable def sum4 (X Y : Finset (ZMod p)) : Finset (ZMod p) :=
  (X * Y + X * Y) + (X * Y + X * Y)

/-- Eight-fold sums of products `xy`. -/
noncomputable def sum8 (X Y : Finset (ZMod p)) : Finset (ZMod p) :=
  sum4 X Y + sum4 X Y

/-- A set with more than `p / 2` elements meets its negative. -/
lemma inter_neg_nonempty (A : Finset (ZMod p)) (hA : p < 2 * #A) :
    (A ∩ A.image fun z ↦ -z).Nonempty := by
  classical
  by_contra hne
  have hd : Disjoint A (A.image fun z ↦ -z) := by
    rw [disjoint_iff_inter_eq_empty]
    exact not_nonempty_iff_eq_empty.mp hne
  have hcardImage : #(A.image fun z ↦ -z) = #A := card_image_iff.mpr neg_injective.injOn
  have hle : #(A ∪ A.image fun z ↦ -z) ≤ p := by
    calc
      _ ≤ #(univ : Finset (ZMod p)) := card_le_card (subset_univ _)
      _ = p := ZMod.card p
  have hsplit := card_union_of_disjoint hd
  omega

/-- **Glibichuk's lemma.** If `|X||Y| > p` and `Y` is antisymmetric, then every residue is a sum
of eight products `xy` with `x ∈ X`, `y ∈ Y`. -/
theorem glibichuk (hp : p.Prime) (hp2 : 2 < p)
    (X Y : Finset (ZMod p)) (hprod : p < #X * #Y) (hanti : Antisymm Y) :
    sum8 X Y = univ := by
  classical
  have := Fact.mk hp
  obtain ⟨ξ, -, hplus, hminus⟩ := exists_two_large_affImg (p := p) hp hp2 X Y hprod
  obtain ⟨z, hz⟩ := inter_neg_nonempty (p := p) (affImg ξ X Y) hplus
  have hz₁ : z ∈ affImg ξ X Y := (mem_inter.mp hz).1
  obtain ⟨z', hz₂, hzz'⟩ := mem_image.mp (mem_inter.mp hz).2
  rw [affImg] at hz₁ hz₂
  obtain ⟨⟨x₁, y₁⟩, hxy₁, h₁⟩ := mem_image.mp hz₁
  obtain ⟨⟨x₂, y₂⟩, hxy₂, h₂⟩ := mem_image.mp hz₂
  obtain ⟨hx₁, hy₁⟩ := mem_product.mp hxy₁
  obtain ⟨hx₂, hy₂⟩ := mem_product.mp hxy₂
  have hc : y₁ + y₂ ≠ 0 := by
    intro hy
    have hy' : y₂ = -y₁ := by linear_combination hy
    exact hanti y₁ hy₁ (hy' ▸ hy₂)
  have hrel : ξ * (y₁ + y₂) = -(x₁ + x₂) := by
    linear_combination h₁ + h₂ - hzz'
  have hmap : Set.MapsTo (fun z ↦ (y₁ + y₂) * z) (affImg (-ξ) X Y) (sum4 X Y) := by
    intro w hw
    rw [affImg] at hw
    obtain ⟨⟨x₃, y₃⟩, hxy₃, rfl⟩ := mem_image.mp hw
    obtain ⟨hx₃, hy₃⟩ := mem_product.mp hxy₃
    have hp₁ : x₃ * y₁ ∈ X * Y := mul_mem_mul hx₃ hy₁
    have hp₂ : x₃ * y₂ ∈ X * Y := mul_mem_mul hx₃ hy₂
    have hp₃ : x₁ * y₃ ∈ X * Y := mul_mem_mul hx₁ hy₃
    have hp₄ : x₂ * y₃ ∈ X * Y := mul_mem_mul hx₂ hy₃
    have heq : (y₁ + y₂) * (x₃ + -ξ * y₃) = x₃ * y₁ + x₃ * y₂ + (x₁ * y₃ + x₂ * y₃) := by
      linear_combination -y₃ * hrel
    show (y₁ + y₂) * (x₃ + -ξ * y₃) ∈ sum4 X Y
    rw [heq]
    exact add_mem_add (add_mem_add hp₁ hp₂) (add_mem_add hp₃ hp₄)
  have hinj : Set.InjOn (fun z ↦ (y₁ + y₂) * z) (affImg (-ξ) X Y) := by
    intro a _ b _ hab
    exact (mul_left_cancel₀ hc) hab
  have h4 : #(affImg (-ξ) X Y) ≤ #(sum4 X Y) := card_le_card_of_injOn _ hmap hinj
  have h4large : p < 2 * #(sum4 X Y) := lt_of_lt_of_le hminus (Nat.mul_le_mul_left 2 h4)
  have h4ne : (sum4 X Y).Nonempty := by
    rw [← card_pos]
    omega
  have hCD := ZMod.cauchy_davenport hp h4ne h4ne
  have h8 : p ≤ #(sum8 X Y) := by
    rw [sum8]
    refine le_trans ?_ hCD
    simp only [le_min_iff]
    exact ⟨le_rfl, by omega⟩
  exact eq_of_subset_of_card_le (subset_univ _) (by simpa using h8)

end Glibichuk

/- Prime blocks -/

section PrimeBlocks

variable {p k L H : ℕ}

/-- The product `∏ᵢ q i (u i)` of the chosen denominators. -/
def denProd (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L) : ℕ :=
  ∏ i, q i (u i)

/-- The numerator of `∑ᵢ 1 / q i (u i)` over the common denominator `denProd q u`. -/
def recNum (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L) : ℕ :=
  ∑ i, ∏ j ∈ univ.erase i, q j (u j)

/-- The residue `∑ᵢ (q i (u i))⁻¹` in `ZMod p`. -/
def recSum (p : ℕ) (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L) : ZMod p :=
  ∑ i, ((q i (u i) : ZMod p)⁻¹)

/-- The set of all residues `recSum p q u`. -/
noncomputable def recSet (p : ℕ) (q : Fin k → Fin L → ℕ) : Finset (ZMod p) :=
  univ.image (recSum p q)

/-- Clearing denominators: `denProd · recSum = recNum` in `ZMod p`. -/
lemma denProd_mul_recSum (hp : p.Prime) (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L)
    (hq_lt : ∀ i j, q i j < p) (hq_pos : ∀ i j, 0 < q i j) :
    (denProd q u : ZMod p) * recSum p q u = recNum q u := by
  classical
  have := Fact.mk hp
  rw [recSum, mul_sum]
  simp only [denProd, recNum, Nat.cast_sum, Nat.cast_prod]
  apply sum_congr rfl
  intro i _
  have hqi : (q i (u i) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (hq_pos i (u i)) (hq_lt i (u i))
  rw [← mul_prod_erase univ (fun j ↦ (q j (u j) : ZMod p)) (mem_univ i)]
  field_simp

/-- `denProd q u ≤ H ^ k`. -/
lemma denProd_le (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L)
    (hq_le : ∀ i j, q i j ≤ H) : denProd q u ≤ H ^ k := by
  calc
    denProd q u ≤ ∏ _i : Fin k, H := prod_le_prod' fun i _ ↦ hq_le i (u i)
    _ = H ^ k := by simp

/-- `recNum q u ≤ k H ^ (k - 1)`. -/
lemma recNum_le (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L) (hq_le : ∀ i j, q i j ≤ H) :
    recNum q u ≤ k * H ^ (k - 1) := by
  calc
    recNum q u ≤ ∑ _i : Fin k, H ^ (k - 1) := by
      apply sum_le_sum
      intro i _
      calc
        ∏ j ∈ univ.erase i, q j (u j) ≤ ∏ _j ∈ univ.erase i, H :=
          prod_le_prod' fun j _ ↦ hq_le j (u j)
        _ = H ^ (k - 1) := by simp [card_erase_of_mem]
    _ = k * H ^ (k - 1) := by simp

/-- If `u i ≠ v i`, the prime `q i (u i)` does not divide `denProd q v`. -/
lemma not_dvd_denProd (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_inj : Function.Injective fun ij : Fin k × Fin L ↦ q ij.1 ij.2)
    {i : Fin k} (hi : u i ≠ v i) : ¬ q i (u i) ∣ denProd q v := by
  intro hd
  rw [denProd] at hd
  obtain ⟨j, _, hj⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp (hq_prime i (u i))) _).mp hd
  have hqeq : q i (u i) = q j (v j) :=
    (Nat.prime_dvd_prime_iff_eq (hq_prime i (u i)) (hq_prime j (v j))).mp hj
  have hpairs : (i, u i) = (j, v j) := hq_inj hqeq
  have hij : i = j := congrArg Prod.fst hpairs
  subst hij
  exact hi (congrArg Prod.snd hpairs)

/-- No chosen prime `q i (u i)` divides `recNum q u`. -/
lemma not_dvd_recNum (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_inj : Function.Injective fun ij : Fin k × Fin L ↦ q ij.1 ij.2)
    (i : Fin k) : ¬ q i (u i) ∣ recNum q u := by
  classical
  let term : Fin k → ℕ := fun a ↦ ∏ j ∈ univ.erase a, q j (u j)
  have hterm : ¬ q i (u i) ∣ term i := by
    apply (Nat.prime_iff.mp (hq_prime i (u i))).not_dvd_finsetProd
    intro j hj hd
    have hqeq : q i (u i) = q j (u j) :=
      (Nat.prime_dvd_prime_iff_eq (hq_prime i (u i)) (hq_prime j (u j))).mp hd
    have hpairs : (i, u i) = (j, u j) := hq_inj hqeq
    exact (mem_erase.mp hj).1 (congrArg Prod.fst hpairs).symm
  have hrest : q i (u i) ∣ ∑ a ∈ univ.erase i, term a := by
    apply dvd_sum
    intro a ha
    apply dvd_prod_of_mem (fun j ↦ q j (u j))
    exact mem_erase.mpr ⟨fun h ↦ (mem_erase.mp ha).1 h.symm, mem_univ i⟩
  have hdecomp : recNum q u = term i + ∑ a ∈ univ.erase i, term a := by
    rw [recNum]
    exact (add_sum_erase univ term (mem_univ i)).symm
  intro hnum
  apply hterm
  rw [hdecomp] at hnum
  exact (Nat.dvd_add_iff_left hrest).mpr hnum

/-- Distinct choice vectors give distinct cross products. -/
lemma cross_ne (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_inj : Function.Injective fun ij : Fin k × Fin L ↦ q ij.1 ij.2)
    (huv : u ≠ v) : recNum q u * denProd q v ≠ recNum q v * denProd q u := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp huv
  have hrD : q i (u i) ∣ denProd q u := by
    rw [denProd]
    exact dvd_prod_of_mem (fun j ↦ q j (u j)) (mem_univ i)
  have hrDv := not_dvd_denProd q u v hq_prime hq_inj hi
  have hrN := not_dvd_recNum q u hq_prime hq_inj i
  intro heq
  have hrLeft : q i (u i) ∣ recNum q u * denProd q v := by
    rw [heq]
    exact dvd_mul_of_dvd_right hrD _
  exact hrN ((hq_prime i (u i)).dvd_mul.mp hrLeft |>.resolve_right hrDv)

/-- `recNum q u · denProd q v ≤ k H ^ (2k - 1)`. -/
lemma cross_le (hk : 0 < k) (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L)
    (hq_le : ∀ i j, q i j ≤ H) : recNum q u * denProd q v ≤ k * H ^ (2 * k - 1) := by
  calc
    recNum q u * denProd q v ≤ (k * H ^ (k - 1)) * H ^ k :=
      Nat.mul_le_mul (recNum_le q u hq_le) (denProd_le q v hq_le)
    _ = k * H ^ (2 * k - 1) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega

/-- If `2 k H ^ (2k - 1) < p`, the map `u ↦ recSum p q u` is injective. -/
lemma recSum_injective (hp : p.Prime) (hk : 0 < k) (q : Fin k → Fin L → ℕ)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_inj : Function.Injective fun ij : Fin k × Fin L ↦ q ij.1 ij.2)
    (hq_le : ∀ i j, q i j ≤ H) (hHlt : H < p) (hsmall : 2 * k * H ^ (2 * k - 1) < p) :
    Function.Injective (recSum p q) := by
  intro u v huv
  by_contra huvne
  have hq_lt : ∀ i j, q i j < p := fun i j ↦ lt_of_le_of_lt (hq_le i j) hHlt
  have hq_pos : ∀ i j, 0 < q i j := fun i j ↦ (hq_prime i j).pos
  have hu := denProd_mul_recSum hp q u hq_lt hq_pos
  have hv := denProd_mul_recSum hp q v hq_lt hq_pos
  set A := recNum q u * denProd q v with hA
  set B := recNum q v * denProd q u with hB
  have hcast : (A : ZMod p) = (B : ZMod p) := by
    rw [hA, hB]
    push_cast
    rw [← hu, ← hv, huv]
    ring
  have hmod : A % p = B % p := (ZMod.natCast_eq_natCast_iff' A B p).mp hcast
  have hAle : A ≤ k * H ^ (2 * k - 1) := cross_le hk q u v hq_le
  have hBle : B ≤ k * H ^ (2 * k - 1) := cross_le hk q v u hq_le
  have hAp : A < p := by nlinarith
  have hBp : B < p := by nlinarith
  rw [Nat.mod_eq_of_lt hAp, Nat.mod_eq_of_lt hBp] at hmod
  exact cross_ne q u v hq_prime hq_inj huvne hmod

/-- Under the same hypotheses there are exactly `L ^ k` residues `recSum p q u`. -/
lemma card_recSet (hp : p.Prime) (hk : 0 < k) (q : Fin k → Fin L → ℕ)
    (hq_prime : ∀ i j, (q i j).Prime)
    (hq_inj : Function.Injective fun ij : Fin k × Fin L ↦ q ij.1 ij.2)
    (hq_le : ∀ i j, q i j ≤ H) (hHlt : H < p) (hsmall : 2 * k * H ^ (2 * k - 1) < p) :
    #(recSet p q) = L ^ k := by
  classical
  rw [recSet, card_image_iff.mpr
    (recSum_injective hp hk q hq_prime hq_inj hq_le hHlt hsmall).injOn]
  simp

/-- `recNum q u > 0`. -/
lemma recNum_pos (hk : 0 < k) (q : Fin k → Fin L → ℕ) (u : Fin k → Fin L)
    (hq_pos : ∀ i j, 0 < q i j) : 0 < recNum q u := by
  rw [recNum]
  apply sum_pos'
  · exact fun _ _ ↦ Nat.zero_le _
  · exact ⟨⟨0, hk⟩, mem_univ _, prod_pos fun j _ ↦ hq_pos j (u j)⟩

/-- The set `recSet p q` contains no pair `y, -y`. -/
lemma recSet_antisymm (hp : p.Prime) (hk : 0 < k) (q : Fin k → Fin L → ℕ)
    (hq_prime : ∀ i j, (q i j).Prime) (hq_le : ∀ i j, q i j ≤ H) (hHlt : H < p)
    (hsmall : 2 * k * H ^ (2 * k - 1) < p) :
    Antisymm (p := p) (recSet p q) := by
  classical
  intro y hy hny
  rw [recSet] at hy hny
  obtain ⟨u, _, rfl⟩ := mem_image.mp hy
  obtain ⟨v, _, hvneg⟩ := mem_image.mp hny
  have hq_lt : ∀ i j, q i j < p := fun i j ↦ lt_of_le_of_lt (hq_le i j) hHlt
  have hq_pos : ∀ i j, 0 < q i j := fun i j ↦ (hq_prime i j).pos
  have hu := denProd_mul_recSum hp q u hq_lt hq_pos
  have hv := denProd_mul_recSum hp q v hq_lt hq_pos
  set A := recNum q u * denProd q v with hA
  set B := recNum q v * denProd q u with hB
  have hsumcast : ((A + B : ℕ) : ZMod p) = 0 := by
    rw [hA, hB]
    push_cast
    rw [← hu, ← hv, hvneg]
    ring
  have hpdiv : p ∣ A + B := (ZMod.natCast_eq_zero_iff (A + B) p).mp hsumcast
  have hAle : A ≤ k * H ^ (2 * k - 1) := cross_le hk q u v hq_le
  have hBle : B ≤ k * H ^ (2 * k - 1) := cross_le hk q v u hq_le
  have hApos : 0 < A := mul_pos (recNum_pos hk q u hq_pos) (prod_pos fun i _ ↦ hq_pos i (v i))
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by nlinarith) hpdiv

/-- The `k²` denominators `q i (u i) · q j (v j)` from expanding `recSum q u · recSum q v`. -/
noncomputable def prodDenoms (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L) : Multiset ℕ :=
  ((univ : Finset (Fin k)) ×ˢ (univ : Finset (Fin k))).val.map
    fun ij ↦ q ij.1 (u ij.1) * q ij.2 (v ij.2)

/-- There are `k²` such denominators. -/
lemma card_prodDenoms (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L) :
    Multiset.card (prodDenoms q u v) = k ^ 2 := by
  simp [prodDenoms, pow_two]

/-- Their inverses sum to `recSum q u · recSum q v`. -/
lemma sum_prodDenoms (hp : p.Prime) (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L) :
    ((prodDenoms q u v).map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = recSum p q u * recSum p q v := by
  have := Fact.mk hp
  rw [prodDenoms, Multiset.map_map, ← Finset.sum_eq_multiset_sum, recSum, recSum,
    Fintype.sum_mul_sum, sum_product]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  simp only [Function.comp_apply, Nat.cast_mul]
  rw [mul_inv_rev, mul_comm]

/-- Each such denominator `n` satisfies `1 ≤ n ≤ p ^ ε` and is coprime to `p`. -/
lemma prodDenoms_admissible (hp : p.Prime) {ε : ℝ} (q : Fin k → Fin L → ℕ) (u v : Fin k → Fin L)
    (hq_prime : ∀ i j, (q i j).Prime) (hq_le : ∀ i j, q i j ≤ H)
    (hHlt : H < p) (hHsq : (H : ℝ) ^ 2 ≤ (p : ℝ) ^ ε) :
    ∀ n ∈ prodDenoms q u v, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p := by
  intro n hn
  rw [prodDenoms, Multiset.mem_map] at hn
  obtain ⟨⟨i, j⟩, -, rfl⟩ := hn
  have hqi_lt : q i (u i) < p := lt_of_le_of_lt (hq_le i (u i)) hHlt
  have hqj_lt : q j (v j) < p := lt_of_le_of_lt (hq_le j (v j)) hHlt
  refine ⟨Nat.one_le_iff_ne_zero.mpr
    (mul_pos (hq_prime i (u i)).pos (hq_prime j (v j)).pos).ne', ?_, ?_⟩
  · refine le_trans ?_ hHsq
    have := Nat.mul_le_mul (hq_le i (u i)) (hq_le j (v j))
    rw [← pow_two] at this
    exact_mod_cast this
  · apply Nat.Coprime.symm
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    rcases hp.dvd_mul.mp hdvd with hdvd | hdvd
    · exact Nat.not_dvd_of_pos_of_lt (hq_prime i (u i)).pos hqi_lt hdvd
    · exact Nat.not_dvd_of_pos_of_lt (hq_prime j (v j)).pos hqj_lt hdvd

/-- Representations add: concatenate the multisets of denominators. -/
lemma represents_add {ε : ℝ} {a b : ZMod p} {s t : Multiset ℕ}
    (hs : _root_.Erdos1180.Represents ε p a s) (ht : _root_.Erdos1180.Represents ε p b t) :
    _root_.Erdos1180.Represents ε p (a + b) (s + t) := by
  refine ⟨fun n hn ↦ ?_, ?_⟩
  · rcases Multiset.mem_add.mp hn with hn | hn
    · exact hs.1 n hn
    · exact ht.1 n hn
  · rw [Multiset.map_add, Multiset.sum_add, hs.2, ht.2]

/-- `a` is a sum of exactly `m` admissible inverses. -/
def ExactRep (ε : ℝ) (p m : ℕ) (a : ZMod p) : Prop :=
  ∃ s : Multiset ℕ, Multiset.card s = m ∧ _root_.Erdos1180.Represents ε p a s

/-- Exact representability is compatible with sumsets. -/
lemma exactRep_add {m n : ℕ} {S T : Finset (ZMod p)} {ε : ℝ}
    (hS : ∀ a ∈ S, ExactRep ε p m a) (hT : ∀ b ∈ T, ExactRep ε p n b) :
    ∀ z ∈ S + T, ExactRep ε p (m + n) z := by
  classical
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hz
  obtain ⟨s, hs, hsr⟩ := hS a ha
  obtain ⟨t, ht, htr⟩ := hT b hb
  exact ⟨s + t, by rw [Multiset.card_add, hs, ht], represents_add hsr htr⟩

/-- Every element of `recSet · recSet` is a sum of exactly `k²` admissible inverses. -/
lemma mul_exactRep (hp : p.Prime) {ε : ℝ} (q : Fin k → Fin L → ℕ)
    (hq_prime : ∀ i j, (q i j).Prime) (hq_le : ∀ i j, q i j ≤ H)
    (hHlt : H < p) (hHsq : (H : ℝ) ^ 2 ≤ (p : ℝ) ^ ε) :
    ∀ z ∈ recSet p q * recSet p q, ExactRep ε p (k ^ 2) z := by
  classical
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp hz
  rw [recSet] at ha hb
  obtain ⟨u, _, rfl⟩ := mem_image.mp ha
  obtain ⟨v, _, rfl⟩ := mem_image.mp hb
  exact ⟨prodDenoms q u v, card_prodDenoms q u v,
    prodDenoms_admissible hp q u v hq_prime hq_le hHlt hHsq, sum_prodDenoms hp q u v⟩

/-- Every element of the eightfold sumset is a sum of exactly `8k²` admissible inverses. -/
lemma sum8_exactRep [NeZero p] (hp : p.Prime) {ε : ℝ} (q : Fin k → Fin L → ℕ)
    (hq_prime : ∀ i j, (q i j).Prime) (hq_le : ∀ i j, q i j ≤ H)
    (hHlt : H < p) (hHsq : (H : ℝ) ^ 2 ≤ (p : ℝ) ^ ε) :
    ∀ z ∈ sum8 (recSet p q) (recSet p q), ExactRep ε p (8 * k ^ 2) z := by
  have h1 := mul_exactRep (ε := ε) hp q hq_prime hq_le hHlt hHsq
  have h2 := exactRep_add h1 h1
  have h4 := exactRep_add h2 h2
  have h8 := exactRep_add h4 h4
  have e : k ^ 2 + k ^ 2 + (k ^ 2 + k ^ 2) + (k ^ 2 + k ^ 2 + (k ^ 2 + k ^ 2)) = 8 * k ^ 2 := by
    ring
  rw [e] at h8
  exact h8

end PrimeBlocks

/- Asymptotic estimates -/

section Asymptotics

open Filter Topology Asymptotics Real

/-- `(n + 1)² ≤ 2 ^ n` for `n ≥ 6`. -/
lemma sq_succ_le_two_pow (n : ℕ) (hn : 6 ≤ n) : (n + 1) ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (n + 1 + 1) ^ 2 ≤ 2 * (n + 1) ^ 2 := by nlinarith
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- `log x ≤ c x ^ r` eventually, for `r, c > 0`. -/
lemma ev_log_le {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, log x ≤ c * x ^ r := by
  have hbound := (isLittleO_log_rpow_atTop hr).bound hc
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, abs_of_nonneg (log_nonneg hx1), Real.norm_eq_abs,
    abs_of_nonneg (rpow_nonneg (by positivity) _)] at hx
  exact hx

/-- `c n ^ a < n ^ b` eventually, for `a < b`. -/
lemma ev_mul_rpow_lt {a b c : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  have ht := tendsto_rpow_atTop (sub_pos.mpr hab)
  have h : ∀ᶠ x : ℝ in atTop, c * x ^ a < x ^ b := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), ht.eventually_gt_atTop c] with x hx hxc
    calc
      c * x ^ a < x ^ (b - a) * x ^ a := mul_lt_mul_of_pos_right hxc (rpow_pos_of_pos hx a)
      _ = x ^ b := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
  exact tendsto_natCast_atTop_atTop.eventually h

/-- `π(n) ≥ n ^ t` eventually, for `t < 1` (from Chebyshev's lower bound). -/
lemma ev_primeCounting_ge {t : ℝ} (ht1 : t < 1) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ t ≤ Nat.primeCounting n := by
  have hlogReal := ev_log_le (sub_pos.mpr ht1) (show 0 < log 2 / 2 by positivity)
  have hlog := tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [eventually_ge_atTop 6, hlog] with n hn hlogn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 6) hn)
  have hlogpos : 0 < log (n : ℝ) := log_pos (by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 6) hn))
  have hsquareR : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
    exact_mod_cast sq_succ_le_two_pow n hn
  have hnum : log ((n : ℝ) + 1) ≤ (n : ℝ) * log 2 / 2 := by
    have hlogpow := log_le_log (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2) hsquareR
    rw [Real.log_pow, Real.log_pow] at hlogpow
    push_cast at hlogpow
    linarith
  refine le_trans ?_ (Chebyshev.pi_ge n)
  rw [le_div_iff₀ hlogpos]
  have hrpow : (n : ℝ) ^ t * (n : ℝ) ^ (1 - t) = n := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hmul := mul_le_mul_of_nonneg_left hlogn (rpow_nonneg hnpos.le t)
  have hmul' : (n : ℝ) ^ t * log n ≤ (n : ℝ) * log 2 / 2 := by
    calc
      _ ≤ (n : ℝ) ^ t * (log 2 / 2 * (n : ℝ) ^ (1 - t)) := hmul
      _ = (log 2 / 2) * ((n : ℝ) ^ t * (n : ℝ) ^ (1 - t)) := by ring
      _ = (n : ℝ) * log 2 / 2 := by rw [hrpow]; ring
  linarith

/-- `⌊n ^ a⌋₊`. -/
noncomputable def fpow (a : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ a⌋₊

/-- `⌊n ^ a⌋₊ ≤ n ^ a`. -/
lemma fpow_le (a : ℝ) (n : ℕ) : (fpow a n : ℝ) ≤ (n : ℝ) ^ a :=
  Nat.floor_le (rpow_nonneg (Nat.cast_nonneg n) a)

/-- `n ^ a / 2 < ⌊n ^ a⌋₊` when `n ^ a ≥ 1`. -/
lemma half_lt_fpow {a : ℝ} {n : ℕ} (hpow : 1 ≤ (n : ℝ) ^ a) : (n : ℝ) ^ a / 2 < fpow a n := by
  simpa [fpow] using Nat.div_two_lt_floor hpow

/-- `⌊n ^ a⌋₊ → ∞` for `a > 0`. -/
lemma tendsto_fpow {a : ℝ} (ha : 0 < a) : Tendsto (fpow a) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  have ht := (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually_ge_atTop (N : ℝ))
  refine ⟨M, fun n hn ↦ ?_⟩
  exact (Nat.le_floor_iff (rpow_nonneg (Nat.cast_nonneg n) a)).mpr (by
    simpa only [Function.comp_apply] using hM n hn)

/-- `⌊n ^ a⌋₊ < n` eventually, for `a < 1`. -/
lemma ev_fpow_lt {a : ℝ} (ha : a < 1) : ∀ᶠ n : ℕ in atTop, fpow a n < n := by
  filter_upwards [ev_mul_rpow_lt (c := 1) ha] with n hn
  have hreal : (fpow a n : ℝ) < n := lt_of_le_of_lt (fpow_le a n) (by simpa using hn)
  exact_mod_cast hreal

/-- `2k ⌊n ^ δ⌋₊ ^ (2k - 1) < n` eventually, when `(2k - 1) δ < 1`. -/
lemma ev_clearing {k : ℕ} {δ : ℝ} (hmargin : ((2 * k - 1 : ℕ) : ℝ) * δ < 1) :
    ∀ᶠ n : ℕ in atTop, 2 * k * (fpow δ n) ^ (2 * k - 1) < n := by
  have hcmp := ev_mul_rpow_lt (c := (2 * k : ℝ)) (a := δ * (2 * k - 1 : ℕ)) (b := 1) (by
    simpa [mul_comm] using hmargin)
  filter_upwards [hcmp] with n hn
  have hpow : ((fpow δ n : ℝ) ^ (2 * k - 1)) ≤ (((n : ℝ) ^ δ) ^ (2 * k - 1)) :=
    pow_le_pow_left₀ (by positivity) (fpow_le δ n) _
  have hreal : ((2 * k * (fpow δ n) ^ (2 * k - 1) : ℕ) : ℝ) < n := by
    calc
      _ = (2 * k : ℝ) * (fpow δ n : ℝ) ^ (2 * k - 1) := by norm_num
      _ ≤ (2 * k : ℝ) * (((n : ℝ) ^ δ) ^ (2 * k - 1)) := by gcongr
      _ = (2 * k : ℝ) * (n : ℝ) ^ (δ * (2 * k - 1 : ℕ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      _ < (n : ℝ) ^ (1 : ℝ) := hn
      _ = n := by simp
  exact_mod_cast hreal

/-- `⌊n ^ δ⌋₊ ² ≤ n ^ ε` when `2δ ≤ ε`. -/
lemma fpow_sq_le {δ ε : ℝ} {n : ℕ} (hn : 1 ≤ n) (hmargin : 2 * δ ≤ ε) :
    (fpow δ n : ℝ) ^ 2 ≤ (n : ℝ) ^ ε := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    (fpow δ n : ℝ) ^ 2 ≤ ((n : ℝ) ^ δ) ^ 2 := pow_le_pow_left₀ (by positivity) (fpow_le δ n) _
    _ = (n : ℝ) ^ (2 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num [mul_comm]
    _ ≤ (n : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hnreal hmargin

/-- `n < ⌊n ^ γ⌋₊ ^ (2k)` eventually, when `2kγ > 1`. -/
lemma ev_lt_fpow_pow {k : ℕ} {γ : ℝ} (hk : 0 < k) (hγ : 0 < γ) (hmargin : 1 < (2 * k : ℝ) * γ) :
    ∀ᶠ n : ℕ in atTop, n < (fpow γ n) ^ (2 * k) := by
  have hcmp := ev_mul_rpow_lt (c := (2 : ℝ) ^ (2 * k : ℕ)) (a := 1) (b := (2 * k : ℕ) * γ) (by
    push_cast
    exact hmargin)
  have hpowOne :=
    ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hcmp, hpowOne] with n hnGrow hnOne
  have hlow := half_lt_fpow hnOne
  have hlowPow : (((n : ℝ) ^ γ / 2) ^ (2 * k)) < (fpow γ n : ℝ) ^ (2 * k) :=
    pow_lt_pow_left₀ hlow (by positivity) (by omega)
  have hbase : (n : ℝ) < ((n : ℝ) ^ γ / 2) ^ (2 * k) := by
    have hpowEq : (n : ℝ) ^ ((2 * k : ℕ) * γ) = ((n : ℝ) ^ γ) ^ (2 * k) := by
      rw [mul_comm, Real.rpow_mul (by positivity), Real.rpow_natCast]
    rw [div_pow, ← hpowEq, lt_div_iff₀ (by positivity)]
    simpa [mul_comm] using hnGrow
  have hreal : (n : ℝ) < (((fpow γ n) ^ (2 * k) : ℕ) : ℝ) := by
    push_cast
    exact hbase.trans hlowPow
  exact_mod_cast hreal

/-- `k ⌊n ^ γ⌋₊ ≤ π(⌊n ^ δ⌋₊)` eventually, when `γ < δ t` with `0 < t < 1`. -/
lemma ev_prime_supply {k : ℕ} {δ γ t : ℝ} (hδ : 0 < δ) (ht0 : 0 < t) (ht1 : t < 1)
    (hmargin : γ < δ * t) :
    ∀ᶠ n : ℕ in atTop, k * fpow γ n ≤ #(Nat.primesLE (fpow δ n)) := by
  have hprimeAtH := (tendsto_fpow hδ).eventually (ev_primeCounting_ge ht1)
  have hcmp := ev_mul_rpow_lt (c := (k : ℝ) * (2 : ℝ) ^ t) (a := γ) (b := δ * t) hmargin
  have hpowOne :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hprimeAtH, hcmp, hpowOne] with n hprime hgrow hnOne
  have hHlow := half_lt_fpow hnOne
  have hHlowPow : (((n : ℝ) ^ δ / 2) ^ t) < (fpow δ n : ℝ) ^ t :=
    Real.rpow_lt_rpow (by positivity) hHlow ht0
  have hbase : (k : ℝ) * (n : ℝ) ^ γ < ((n : ℝ) ^ δ / 2) ^ t := by
    rw [Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul (by positivity),
      lt_div_iff₀ (rpow_pos_of_pos (by norm_num) _)]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hgrow
  have hKLreal : ((k * fpow γ n : ℕ) : ℝ) ≤ Nat.primeCounting (fpow δ n) := by
    apply le_of_lt
    calc
      _ = (k : ℝ) * (fpow γ n : ℝ) := by norm_num
      _ ≤ (k : ℝ) * (n : ℝ) ^ γ := by
        gcongr
        exact fpow_le γ n
      _ < ((n : ℝ) ^ δ / 2) ^ t := hbase
      _ < (fpow δ n : ℝ) ^ t := hHlowPow
      _ ≤ Nat.primeCounting (fpow δ n) := hprime
  rw [Nat.primesLE_card_eq_primeCounting]
  exact_mod_cast hKLreal

/-- All size conditions needed for the prime-block construction at the prime `n`, with
`H = ⌊n ^ δ⌋₊` and `L = ⌊n ^ γ⌋₊`. -/
def Good (ε : ℝ) (k : ℕ) (δ γ : ℝ) (n : ℕ) : Prop :=
  2 < n ∧
  fpow δ n < n ∧
  2 * k * (fpow δ n) ^ (2 * k - 1) < n ∧
  (fpow δ n : ℝ) ^ 2 ≤ (n : ℝ) ^ ε ∧
  n < (fpow γ n) ^ (2 * k) ∧
  k * fpow γ n ≤ #(Nat.primesLE (fpow δ n))

/-- Under the margin conditions, all large `n` are good. -/
lemma ev_good {ε δ γ t : ℝ} {k : ℕ}
    (hk : 0 < k) (hδ : 0 < δ) (hγ : 0 < γ) (hδone : δ < 1)
    (hclear : ((2 * k - 1 : ℕ) : ℝ) * δ < 1)
    (hdenom : 2 * δ ≤ ε) (hgrow : 1 < (2 * k : ℝ) * γ)
    (ht0 : 0 < t) (ht1 : t < 1) (hsupply : γ < δ * t) :
    ∀ᶠ n : ℕ in atTop, Good ε k δ γ n := by
  filter_upwards [eventually_gt_atTop 2, ev_fpow_lt hδone, ev_clearing (k := k) hclear,
    ev_lt_fpow_pow hk hγ hgrow, ev_prime_supply (k := k) hδ ht0 ht1 hsupply]
    with n hn hHn hsmalln hlargen hprimesn
  exact ⟨hn, hHn, hsmalln, fpow_sq_le (by omega) hdenom, hlargen, hprimesn⟩

/-- A choice of parameters satisfying the margin conditions, for any `ε > 0`. -/
lemma choose_params {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (δ γ t : ℝ),
      0 < k ∧ 0 < δ ∧ 0 < γ ∧ δ < 1 ∧
      ((2 * k - 1 : ℕ) : ℝ) * δ < 1 ∧
      2 * δ ≤ ε ∧ 1 < (2 * k : ℝ) * γ ∧
      0 < t ∧ t < 1 ∧ γ < δ * t := by
  obtain ⟨k, hkbig⟩ := exists_nat_gt (2 / ε + 1)
  have hkR : (1 : ℝ) < k := by
    have : 0 < 2 / ε := div_pos (by norm_num) hε
    linarith
  have hk : 0 < k := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hkR)
  set d : ℝ := 4 * k - 1 with hd
  set δ : ℝ := 2 / d with hδdef
  set s : ℝ := 1 / (2 * k) with hsdef
  set γ : ℝ := (δ + s) / 2 with hγdef
  set t : ℝ := (γ / δ + 1) / 2 with htdef
  have h2kpos : (0 : ℝ) < 2 * k := by positivity
  have hdpos : 0 < d := by rw [hd]; linarith
  have hδ : 0 < δ := div_pos (by norm_num) hdpos
  have hs : 0 < s := div_pos (by norm_num) h2kpos
  have hsδ : s < δ := by
    rw [hsdef, hδdef, div_lt_div_iff₀ h2kpos hdpos, hd]
    linarith
  have hγ : 0 < γ := by rw [hγdef]; positivity
  have hγδ : γ < δ := by rw [hγdef]; linarith
  have hδone : δ < 1 := by
    rw [hδdef, div_lt_one hdpos, hd]
    linarith
  have hclear : ((2 * k - 1 : ℕ) : ℝ) * δ < 1 := by
    have hkcast : (((2 * k - 1 : ℕ) : ℝ)) = 2 * (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
      norm_num
    rw [hkcast, hδdef, ← mul_div_assoc, div_lt_one hdpos, hd]
    linarith
  have hkε : 2 + ε < (k : ℝ) * ε := by
    calc
      2 + ε = (2 / ε + 1) * ε := by field_simp
      _ < (k : ℝ) * ε := mul_lt_mul_of_pos_right hkbig hε
  have hdenom : 2 * δ ≤ ε := by
    have hfour : (4 : ℝ) < ε * d := by
      rw [hd]
      nlinarith
    rw [hδdef, show 2 * (2 / d) = 4 / d by ring, div_le_iff₀ hdpos]
    linarith
  have hgrow : 1 < (2 * k : ℝ) * γ := by
    have hone : (2 * k : ℝ) * s = 1 := by rw [hsdef]; field_simp
    calc
      1 = (2 * k : ℝ) * s := hone.symm
      _ < (2 * k : ℝ) * γ := mul_lt_mul_of_pos_left (by rw [hγdef]; linarith) h2kpos
  have hratio0 : 0 < γ / δ := div_pos hγ hδ
  have hratio1 : γ / δ < 1 := (div_lt_one hδ).mpr hγδ
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t < 1 := by rw [htdef]; linarith
  have hdt : δ * t = (γ + δ) / 2 := by
    rw [htdef]
    field_simp
  have hsupply : γ < δ * t := by rw [hdt]; linarith
  exact ⟨k, δ, γ, t, hk, hδ, hγ, hδone, hclear, hdenom, hgrow, ht0, ht1, hsupply⟩

end Asymptotics

/- Assembly -/

/-- For a good prime, every residue is a sum of exactly `8k²` admissible inverses. -/
lemma exactRep_of_good {ε δ γ : ℝ} {k p : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hpar : Good ε k δ γ p) (a : ZMod p) : ExactRep ε p (8 * k ^ 2) a := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hp2, hHlt, hsmall, hHsq, hlarge, hsupply⟩ := hpar
  have hcard : Fintype.card (Fin k × Fin (fpow γ p)) ≤ #(Nat.primesLE (fpow δ p)) := by
    simpa using hsupply
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hcard
  let q : Fin k → Fin (fpow γ p) → ℕ := fun i j ↦ e (i, j)
  have hq_mem : ∀ i j, q i j ∈ Nat.primesLE (fpow δ p) := fun i j ↦ he ⟨(i, j), rfl⟩
  have hq_prime : ∀ i j, (q i j).Prime := fun i j ↦ Nat.prime_of_mem_primesLE (hq_mem i j)
  have hq_le : ∀ i j, q i j ≤ fpow δ p := fun i j ↦ Nat.le_of_mem_primesLE (hq_mem i j)
  have hq_inj : Function.Injective (fun ij : Fin k × Fin (fpow γ p) ↦ q ij.1 ij.2) := by
    intro x y hxy
    exact e.injective hxy
  have hcardB : #(recSet p q) = (fpow γ p) ^ k :=
    card_recSet hp hk q hq_prime hq_inj hq_le hHlt hsmall
  have hprod : p < #(recSet p q) * #(recSet p q) := by
    rw [hcardB, ← pow_add, ← two_mul]
    exact hlarge
  have hanti := recSet_antisymm hp hk q hq_prime hq_le hHlt hsmall
  have hcover := glibichuk hp hp2 (recSet p q) (recSet p q) hprod hanti
  have ha : a ∈ sum8 (recSet p q) (recSet p q) := by rw [hcover]; exact mem_univ a
  exact sum8_exactRep hp q hq_prime hq_le hHlt hHsq a ha

/-- The upstream statement `Erdos1180.erdos_1180` (Glibichuk's theorem): for every `ε > 0`
there is `C` such that, for every prime `p`, every residue mod `p` is a sum of at most `C`
inverses of integers `1 ≤ n ≤ p ^ ε`. -/
theorem exists_bound (ε : ℝ) (hε : 0 < ε) : ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
    ∃ s : Multiset ℕ, Multiset.card s ≤ C ∧ _root_.Erdos1180.Represents ε p a s := by
  obtain ⟨k, δ, γ, t, hk, hδ, hγ, hδone, hclear, hdenom, hgrow, ht0, ht1, hsupply⟩ :=
    choose_params hε
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.1
    (ev_good hk hδ hγ hδone hclear hdenom hgrow ht0 ht1 hsupply)
  refine ⟨max (8 * k ^ 2) P₀, fun p hp a ↦ ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases hlarge : P₀ ≤ p
  · obtain ⟨s, hs, hrep⟩ := exactRep_of_good hp hk (hP₀ p hlarge) a
    exact ⟨s, hs ▸ le_max_left _ _, hrep⟩
  · -- small primes: use `a.val` copies of the denominator `1`
    refine ⟨Multiset.replicate a.val 1, ?_, ?_, ?_⟩
    · rw [Multiset.card_replicate]
      exact (a.val_lt.trans (Nat.lt_of_not_ge hlarge)).le.trans (le_max_right _ _)
    · intro n hn
      rw [Multiset.eq_of_mem_replicate hn]
      refine ⟨le_rfl, ?_, Nat.coprime_one_left p⟩
      rw [Nat.cast_one]
      exact Real.one_le_rpow (by exact_mod_cast hp.one_le) hε.le
    · simp

/- The refutation -/

section Refutation

open Filter Topology

/-- If `p < 2 ^ k`, the only positive integer `n ≤ p ^ (1 / k)` is `n = 1`. -/
theorem eq_one_of_le_rpow {k p n : ℕ} (hk : 0 < k) (hp : p < 2 ^ k)
    (h1 : 1 ≤ n) (hn : (n : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / k)) : n = 1 := by
  by_contra hne
  have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / k) := by
    have : 2 ≤ n := by omega
    exact le_trans (by exact_mod_cast this) hn
  have hpow : (2 : ℝ) ^ k ≤ ((p : ℝ) ^ ((1 : ℝ) / k)) ^ k := pow_le_pow_left₀ (by norm_num) h2 k
  have e : ((p : ℝ) ^ ((1 : ℝ) / k)) ^ k = p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p),
      one_div_mul_cancel (by positivity), Real.rpow_one]
  rw [e] at hpow
  have : (p : ℝ) < 2 ^ k := by exact_mod_cast hp
  linarith

/-- If `p < 2 ^ k`, every representation of `-1` with exponent `1 / k` has at least `p - 1`
summands, since all denominators equal `1`. -/
theorem card_ge_of_represents_neg_one {k p : ℕ} (hk : 0 < k) (hp : p.Prime) (hpk : p < 2 ^ k)
    {s : Multiset ℕ} (hs : _root_.Erdos1180.Represents ((1 : ℝ) / k) p (-1) s) :
    p - 1 ≤ Multiset.card s := by
  have := Fact.mk hp
  obtain ⟨hmem, hsum⟩ := hs
  have hall : ∀ n ∈ s, n = 1 := fun n hn =>
    eq_one_of_le_rpow hk hpk (hmem n hn).1 (hmem n hn).2.1
  have hs1 : s = Multiset.replicate (Multiset.card s) 1 := Multiset.eq_replicate_card.mpr hall
  rw [hs1] at hsum
  simp only [Multiset.map_replicate, Nat.cast_one, inv_one, Multiset.sum_replicate,
    nsmul_eq_mul, mul_one] at hsum
  have h0 : ((Multiset.card s + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [hsum]
    ring
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd (by omega) h0
  omega

/-- `(m + 1) ^ 2 < 2 ^ m` for `m ≥ 6`. -/
theorem sq_succ_lt_two_pow (m : ℕ) (hm : 6 ≤ m) : (m + 1) ^ 2 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (n + 1 + 1) ^ 2 ≤ 2 * (n + 1) ^ 2 := by nlinarith
        _ < 2 * 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- The upstream statement `erdos_1180.variants.optimal` is false. -/
theorem not_erdos_1180_variants_optimal :
    ¬ (type_of% @_root_.Erdos1180.erdos_1180.variants.optimal) := by
  intro H
  have h1 := H 1 one_pos
  have ht : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Eventually.of_forall fun m => by
        simp only [Set.mem_Ioi]
        positivity
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually h1)
  set m := M + 10 with hmdef
  have hm := hM m (by omega)
  have hk : (0 : ℕ) < m + 1 := by omega
  have hcast : (1 : ℝ) / ((m : ℝ) + 1) = (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by push_cast; rfl
  rw [hcast] at hm
  have hinv : ((1 : ℝ) / ((m + 1 : ℕ) : ℝ))⁻¹ ^ ((1 : ℝ) + 1) = (((m + 1) ^ 2 : ℕ) : ℝ) := by
    rw [one_div, inv_inv, show ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    ring
  rw [hinv] at hm
  -- a Bertrand prime in `(2 ^ m, 2 ^ (m + 1))`
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ m) (by positivity)
  have h2m : 2 < 2 ^ m := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hplt : p < 2 ^ (m + 1) := by
    rcases lt_or_eq_of_le hle with h | h
    · rw [pow_succ]; omega
    · exfalso
      have hdvd : 2 ∣ p := ⟨2 ^ m, by rw [h]⟩
      rcases hp.eq_one_or_self_of_dvd 2 hdvd with h' | h'
      · omega
      · omega
  -- the set defining `C ε` is nonempty, so `C ε` belongs to it
  set ε : ℝ := (1 : ℝ) / ((m + 1 : ℕ) : ℝ) with hεdef
  have hεpos : 0 < ε := by positivity
  obtain ⟨C₀, hC₀⟩ := exists_bound ε hεpos
  have hmem : _root_.Erdos1180.C ε ∈ {C : ℕ | ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, s.card ≤ C ∧ _root_.Erdos1180.Represents ε p a s} :=
    Nat.sInf_mem ⟨C₀, hC₀⟩
  obtain ⟨s, hscard, hs⟩ := hmem p hp (-1)
  have hge := card_ge_of_represents_neg_one hk hp hplt hs
  have hbig : 2 ^ m ≤ _root_.Erdos1180.C ε := by omega
  have hsmall := sq_succ_lt_two_pow m (by omega)
  have : ((2 ^ m : ℕ) : ℝ) ≤ (_root_.Erdos1180.C ε : ℝ) := by exact_mod_cast hbig
  have : (((m + 1) ^ 2 : ℕ) : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hsmall
  linarith

end Refutation

end Math0.Erdos1180

#math0_refutes Math0.Erdos1180.not_erdos_1180_variants_optimal Erdos1180.erdos_1180.variants.optimal
