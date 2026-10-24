/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Arxiv.«2605.12342».Conjecture1
import Math0.Audit

/-!
# `Γ_{3⊕3}` is not 2-generated

Fernandes [arXiv:2605.12342] studies `Γ_{m⊕n} ≤ S_m × S_n`, the pairs of permutations with equal
sign, and records that `Γ_{3⊕3}` has rank `3`. We prove exactly the formal statement
`Arxiv.«2605.12342».conjecture_1.variants.rank_3_3`: no two elements generate `Γ_{3⊕3}`.
The group is `(C₃ × C₃) ⋊ C₂` with `C₂` acting by inversion: the even part `A₃ × A₃` is abelian
of exponent `3`, and each odd element `x` is an involution with `x n x⁻¹ = n⁻¹` for even `n`
(checked by `decide` on `S₃`). Two even elements only generate even elements. If `x` is odd,
then `⟨x, y⟩ ⊆ ⟨c⟩ ∪ x⟨c⟩` for an even `c` (namely `y` or `x y`), and its even part
`{1, c, c²}` misses `(ρ, 1)` or `(1, ρ)`, where `ρ` is a 3-cycle.
-/

open Arxiv.«2605.12342» Equiv.Perm

namespace Math0.Arxiv.«2605.12342»

-- Helpers live in `Rank33` to avoid clashes with sibling files for the same paper.
namespace Rank33

/-- Membership in `Γ_{3⊕3}` means the two components have the same sign. -/
lemma mem_gamma {g : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)} :
    g ∈ gammaSubgroup 3 3 ↔ sign g.1 = sign g.2 := by
  simp only [gammaSubgroup, signDiffHom, MonoidHom.mem_ker, MonoidHom.mul_apply,
    MonoidHom.inv_apply, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
    MonoidHom.coe_snd, mul_inv_eq_one]

/-- The parity homomorphism on `Γ_{3⊕3}`: the sign of the first (equivalently second)
component. -/
noncomputable def par : gammaSubgroup 3 3 →* ℤˣ :=
  (sign.comp (MonoidHom.fst _ _)).comp (gammaSubgroup 3 3).subtype

/-- `par g` is the sign of the first component. -/
lemma par_apply (g : gammaSubgroup 3 3) :
    par g = sign (g : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)).1 := rfl

/-- The second component has the same sign as the first. -/
lemma sign_snd (g : gammaSubgroup 3 3) :
    sign (g : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)).2 = par g :=
  (mem_gamma.1 g.2).symm

/-- Odd permutations of `Fin 3` are involutions. -/
lemma perm_sq_of_odd : ∀ a : Equiv.Perm (Fin 3), sign a = -1 → a * a = 1 := by decide

/-- Even permutations of `Fin 3` have order dividing `3`. -/
lemma perm_cube_of_even : ∀ a : Equiv.Perm (Fin 3), sign a = 1 → a ^ 3 = 1 := by decide

/-- Odd permutations of `Fin 3` invert even ones by conjugation. -/
lemma perm_conj_of_odd : ∀ x n : Equiv.Perm (Fin 3), sign x = -1 → sign n = 1 →
    x * n * x⁻¹ = n⁻¹ := by decide

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` used to build the two separating elements. -/
def rot3 : Equiv.Perm (Fin 3) := finRotate 3

/-- For an even pair `c`, the set `{1, c, c²}` cannot contain both `(rot3, 1)` and `(1, rot3)`. -/
lemma perm_sep : ∀ c : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), sign c.1 = 1 → sign c.2 = 1 →
    ¬ ((((rot3, 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = 1 ∨
          (rot3, 1) = c ∨ (rot3, 1) = c ^ 2) ∧
        (((1, rot3) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = 1 ∨
          (1, rot3) = c ∨ (1, rot3) = c ^ 2)) := by
  unfold rot3
  decide

/-- Odd elements of `Γ_{3⊕3}` are involutions. -/
lemma sq_eq_one {g : gammaSubgroup 3 3} (h : par g = -1) : g * g = 1 := by
  have h2 := sign_snd g
  rw [h] at h2
  rw [par_apply] at h
  apply Subtype.ext
  ext1
  · exact perm_sq_of_odd _ h
  · exact perm_sq_of_odd _ h2

/-- Even elements of `Γ_{3⊕3}` have order dividing `3`. -/
lemma cube_eq_one {g : gammaSubgroup 3 3} (h : par g = 1) : g ^ 3 = 1 := by
  have h2 := sign_snd g
  rw [h] at h2
  rw [par_apply] at h
  apply Subtype.ext
  ext1
  · exact perm_cube_of_even _ h
  · exact perm_cube_of_even _ h2

/-- Odd elements of `Γ_{3⊕3}` invert even ones by conjugation. -/
lemma conj_eq_inv {x n : gammaSubgroup 3 3} (hx : par x = -1) (hn : par n = 1) :
    x * n * x⁻¹ = n⁻¹ := by
  have hx2 := sign_snd x
  have hn2 := sign_snd n
  rw [hx] at hx2
  rw [hn] at hn2
  rw [par_apply] at hx hn
  apply Subtype.ext
  ext1
  · exact perm_conj_of_odd _ _ hx hn
  · exact perm_conj_of_odd _ _ hx2 hn2

/-- For `x` odd and `c` even, the set `{c ^ k} ∪ {x * c ^ k}` is a subgroup of `Γ_{3⊕3}`. -/
def dihedralSub (x c : gammaSubgroup 3 3) (hx : par x = -1) (hc : par c = 1) :
    Subgroup (gammaSubgroup 3 3) where
  carrier := {g | ∃ k : ℤ, g = c ^ k ∨ g = x * c ^ k}
  one_mem' := ⟨0, Or.inl (zpow_zero c).symm⟩
  mul_mem' := by
    have hxx : x * x = 1 := sq_eq_one hx
    have hcomm : ∀ k : ℤ, c ^ k * x = x * c ^ (-k) := by
      intro k
      have h1 : x * c ^ (-k) * x⁻¹ = c ^ k := by
        rw [← conj_zpow, conj_eq_inv hx hc, inv_zpow', neg_neg]
      rw [← h1, mul_assoc, inv_mul_cancel, mul_one]
    rintro a b ⟨k, rfl | rfl⟩ ⟨l, rfl | rfl⟩
    · exact ⟨k + l, Or.inl (zpow_add c k l).symm⟩
    · refine ⟨-k + l, Or.inr ?_⟩
      rw [← mul_assoc, hcomm, mul_assoc, zpow_add]
    · refine ⟨k + l, Or.inr ?_⟩
      rw [mul_assoc, zpow_add]
    · refine ⟨-k + l, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc (c ^ k), hcomm, ← mul_assoc, ← mul_assoc, hxx, one_mul,
        zpow_add]
  inv_mem' := by
    have hxx : x * x = 1 := sq_eq_one hx
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have hcomm : ∀ k : ℤ, c ^ k * x = x * c ^ (-k) := by
      intro k
      have h1 : x * c ^ (-k) * x⁻¹ = c ^ k := by
        rw [← conj_zpow, conj_eq_inv hx hc, inv_zpow', neg_neg]
      rw [← h1, mul_assoc, inv_mul_cancel, mul_one]
    rintro a ⟨k, rfl | rfl⟩
    · exact ⟨-k, Or.inl (zpow_neg c k).symm⟩
    · refine ⟨k, Or.inr ?_⟩
      rw [mul_inv_rev, hxinv, ← zpow_neg, hcomm, neg_neg]

/-- If `x` is odd, then `x` and any `y` do not generate `Γ_{3⊕3}`. -/
lemma closure_ne_top_of_odd (x y : gammaSubgroup 3 3) (hx : par x = -1) :
    Subgroup.closure {x, y} ≠ ⊤ := by
  obtain ⟨c, hc, hy⟩ : ∃ c : gammaSubgroup 3 3, par c = 1 ∧ (y = c ∨ y = x * c) := by
    rcases Int.units_eq_one_or (par y) with h | h
    · exact ⟨y, h, Or.inl rfl⟩
    · refine ⟨x * y, ?_, Or.inr ?_⟩
      · rw [map_mul, hx, h]; rfl
      · rw [← mul_assoc, sq_eq_one hx, one_mul]
  intro htop
  have hle : Subgroup.closure {x, y} ≤ dihedralSub x c hx hc := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨0, Or.inr (by simp)⟩
    · rcases hy with rfl | rfl
      · exact ⟨1, Or.inl (by simp)⟩
      · exact ⟨1, Or.inr (by simp)⟩
  rw [htop] at hle
  have key : ∀ g : gammaSubgroup 3 3, par g = 1 → g = 1 ∨ g = c ∨ g = c ^ 2 := by
    intro g hg
    obtain ⟨k, hk | hk⟩ := hle (Subgroup.mem_top g)
    · subst hk
      rw [zpow_eq_zpow_emod' k (cube_eq_one hc)]
      have : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
      rcases this with h | h | h <;> rw [h]
      · left; simp
      · right; left; simp
      · right; right; rfl
    · subst hk
      rw [map_mul, map_zpow, hx, hc, one_zpow, mul_one] at hg
      exact absurd hg (by decide)
  have hA : ((rot3, 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∈ gammaSubgroup 3 3 :=
    mem_gamma.2 (by unfold rot3; decide)
  have hB : ((1, rot3) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∈ gammaSubgroup 3 3 :=
    mem_gamma.2 (by unfold rot3; decide)
  have hrot3 : sign rot3 = 1 := by unfold rot3; decide
  have kA := key ⟨_, hA⟩ hrot3
  have kB := key ⟨_, hB⟩ (sign_one : sign (1 : Equiv.Perm (Fin 3)) = 1)
  have hc2 := sign_snd c
  rw [hc] at hc2
  rw [par_apply] at hc
  apply perm_sep _ hc hc2
  constructor
  · rcases kA with h | h | h
    · left; exact congrArg Subtype.val h
    · right; left; exact congrArg Subtype.val h
    · right; right; exact congrArg Subtype.val h
  · rcases kB with h | h | h
    · left; exact congrArg Subtype.val h
    · right; left; exact congrArg Subtype.val h
    · right; right; exact congrArg Subtype.val h

/-- If `x` and `y` are both even, they only generate the even part, a proper subgroup. -/
lemma closure_ne_top_of_even (x y : gammaSubgroup 3 3) (hx : par x = 1) (hy : par y = 1) :
    Subgroup.closure {x, y} ≠ ⊤ := by
  intro htop
  have hle : Subgroup.closure {x, y} ≤ par.ker := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hx
    · exact hy
  rw [htop] at hle
  have hS : ((Equiv.swap 0 1, Equiv.swap 0 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∈
      gammaSubgroup 3 3 := mem_gamma.2 rfl
  have h := hle (Subgroup.mem_top ⟨_, hS⟩)
  rw [MonoidHom.mem_ker, par_apply] at h
  exact absurd h (by decide : ¬ sign (Equiv.swap (0 : Fin 3) 1) = 1)

end Rank33

open Rank33

/-- **`Γ_{3⊕3}` is not 2-generated** (Fernandes): no two elements of the group of pairs of
permutations of `Fin 3` with equal sign generate it. -/
theorem rank_3_3 : type_of% @Arxiv.«2605.12342».conjecture_1.variants.rank_3_3 := by
  intro h₁ h₂
  rcases Int.units_eq_one_or (par h₁) with e1 | o1
  · rcases Int.units_eq_one_or (par h₂) with e2 | o2
    · exact closure_ne_top_of_even h₁ h₂ e1 e2
    · rw [Set.pair_comm]
      exact closure_ne_top_of_odd h₂ h₁ o2
  · exact closure_ne_top_of_odd h₁ h₂ o1

end Math0.Arxiv.«2605.12342»

#math0_proves Math0.Arxiv.«2605.12342».rank_3_3 Arxiv.«2605.12342».conjecture_1.variants.rank_3_3
