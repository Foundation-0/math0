/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1119»
import Math0.Audit

/-!
# Erdős's answer to Wetzel's problem (Erdős Problem 1119, variant)

Wetzel asked whether a family of entire functions taking only countably many values at each
point of `ℂ` must itself be countable. Erdős [Er64g] showed that the answer is yes when
`ℵ₁ < 𝔠`; we prove the upstream formal statement `erdos_1119.variants.erdos_wetzel`.
If the family `F` were uncountable, choose `G ⊆ F` with `#G = ℵ₁`. By the identity theorem two
distinct entire functions agree only on a discrete, hence countable, subset of `ℂ`, so the union
`S` of all coincidence sets of distinct pairs from `G` has cardinality at most
`ℵ₁ · ℵ₁ · ℵ₀ = ℵ₁ < 𝔠 = #ℂ`. A point `z ∉ S` makes `f ↦ f z` injective on `G`, so `F` takes
`ℵ₁` (uncountably many) values at `z`, a contradiction.
-/

namespace Math0.Erdos1119

open Cardinal Set Filter Topology

/-- Two distinct entire functions agree on only countably many points: by the identity theorem
their coincidence set is discrete, and a discrete subset of `ℂ` is countable. -/
theorem countable_setOf_eq {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : f ≠ g) : {z | f z = g z}.Countable := by
  have hfa : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g univ := fun z _ => hg.analyticAt z
  rcases hfa.eqOn_or_eventually_ne_of_preconnected hga isPreconnected_univ with h | h
  · exact absurd (funext fun z => h (mem_univ z)) hfg
  · have := isDiscrete_of_codiscreteWithin (U := univ) (s := {z | f z = g z}) h
    simpa using (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete this

universe u

/-- The hypothesis `ℵ₁ < 𝔠` does not depend on the universe in which it is stated. -/
theorem aleph_one_lt_continuum_zero (h : (ℵ_ 1 : Cardinal.{u}) < 𝔠) :
    (ℵ_ 1 : Cardinal.{0}) < 𝔠 := by
  rw [← lift_lt.{0, u}, lift_aleph, Ordinal.lift_one, lift_continuum]
  exact h

/-- **Erdős–Wetzel.** If `ℵ₁ < 𝔠`, then every family of entire functions taking only countably
many distinct values at each point of `ℂ` is countable. -/
theorem erdos_wetzel : type_of% @Erdos1119.erdos_1119.variants.erdos_wetzel := by
  intro h F hF hval
  by_contra hFc
  -- an uncountable family contains a subfamily `G` of cardinality exactly `ℵ₁`
  have h1 : ℵ₁ ≤ #F := by
    rw [aleph_one_le_iff]
    exact lt_of_not_ge fun h' => hFc (le_aleph0_iff_set_countable.mp h')
  obtain ⟨G, hGF, hG⟩ := le_mk_iff_exists_subset.mp h1
  -- coincidence sets of distinct pairs from `G`
  let A : G × G → Set ℂ := fun p => {z | p.1.1 z = p.2.1 z ∧ p.1 ≠ p.2}
  have hA : ∀ p, (A p).Countable := by
    intro p
    by_cases hp : p.1 = p.2
    · simp [A, hp]
    · exact (countable_setOf_eq (hF _ (hGF p.1.2)) (hF _ (hGF p.2.2))
        (fun e => hp (Subtype.ext e))).mono (fun z hz => hz.1)
  -- their union has cardinality at most `ℵ₁`
  have hS : #(⋃ p, A p) ≤ ℵ₁ := by
    calc #(⋃ p, A p) ≤ #(G × G) * ⨆ p, #(A p) := mk_iUnion_le _
    _ ≤ ℵ₁ * ℵ₀ := by
        gcongr
        · rw [mk_prod, lift_id, hG, mul_eq_self (aleph0_le_aleph 1)]
        · exact ciSup_le' fun p => le_aleph0_iff_set_countable.mpr (hA p)
    _ = ℵ₁ := by
        rw [mul_eq_max (aleph0_le_aleph 1) le_rfl]
        exact max_eq_left (aleph0_le_aleph 1)
  -- since `ℵ₁ < 𝔠 = #ℂ`, some point `z` lies outside the union
  have hex : ∃ z, z ∉ ⋃ p, A p := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have : #(⋃ p, A p) = 𝔠 := by rw [eq_univ_of_forall hall, mk_univ_complex]
    exact absurd (hS.trans_lt (aleph_one_lt_continuum_zero h)) (by rw [this]; exact lt_irrefl _)
  obtain ⟨z, hz⟩ := hex
  -- evaluation at `z` is injective on `G`, so `F` takes uncountably many values at `z`
  have hinj : InjOn (fun f : ℂ → ℂ => f z) G := by
    intro f hf g hg hfg
    by_contra hne
    exact hz (mem_iUnion.mpr ⟨(⟨f, hf⟩, ⟨g, hg⟩), hfg, fun e => hne (congrArg Subtype.val e)⟩)
  have himg : #((fun f : ℂ → ℂ => f z) '' G) = ℵ₁ := by
    rw [mk_image_eq_of_injOn _ _ hinj, hG]
  have hsub : (fun f : ℂ → ℂ => f z) '' G ⊆ {y | ∃ f ∈ F, f z = y} := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨f, hGF hf, rfl⟩
  have hc := (hval z).mono hsub
  rw [← le_aleph0_iff_set_countable, himg] at hc
  exact absurd hc (not_le.mpr aleph0_lt_aleph_one)

end Math0.Erdos1119

#math0_proves Math0.Erdos1119.erdos_wetzel Erdos1119.erdos_1119.variants.erdos_wetzel
