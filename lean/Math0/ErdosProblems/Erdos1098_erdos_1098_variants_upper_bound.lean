/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1098»
import Math0.Audit

/-!
# Erdős Problem 1098: cliques in the non-commuting graph are bounded by the index of the centre

Let `Γ(G)` be the non-commuting graph of a group `G` (vertices the elements of `G`, with `g ~ h`
iff `gh ≠ hg`); see erdosproblems.com/1098 and Neumann [Ne76]. We prove Neumann's remark, exactly
as stated upstream: if the centre `Z(G)` has finite index `n`, then `Γ(G)` has no clique on
`n + 1` vertices. The proof is a pigeonhole argument: two distinct vertices of a clique cannot lie
in the same coset of `Z(G)`, since then `y = x z` with `z` central and `x, y` would commute; so a
clique injects into `G ⧸ Z(G)`, which has exactly `n` elements.
-/

namespace Math0.Erdos1098

/-- Two elements in the same left coset of the centre commute. -/
theorem commute_of_mk_eq {G : Type*} [Group G] {x y : G}
    (h : (QuotientGroup.mk x : G ⧸ Subgroup.center G) = QuotientGroup.mk y) :
    x * y = y * x := by
  rw [QuotientGroup.eq] at h
  have hz := Subgroup.mem_center_iff.mp h
  have hy : y = x * (x⁻¹ * y) := by group
  rw [hy]
  have := hz x
  calc x * (x * (x⁻¹ * y)) = x * ((x⁻¹ * y) * x) := by rw [this]
    _ = x * (x⁻¹ * y) * x := by group

/-- A clique of the non-commuting graph maps injectively to `G ⧸ Z(G)`. -/
theorem injOn_mk_of_isClique {G : Type*} [Group G] {t : Finset G}
    (ht : (_root_.Erdos1098.nonCommutingGraph G).IsClique (t : Set G)) :
    Set.InjOn (QuotientGroup.mk : G → G ⧸ Subgroup.center G) (t : Set G) := by
  intro x hx y hy hxy
  by_contra hne
  exact ht hx hy hne (commute_of_mk_eq hxy)

/-- If the centre of `G` has finite index `n`, then the non-commuting graph of `G` contains no
complete subgraph on `n + 1` vertices. -/
theorem upper_bound : type_of% @Erdos1098.erdos_1098.variants.upper_bound := by
  intro G _ _ t ht
  have hfin : Finite (G ⧸ Subgroup.center G) := Subgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (G ⧸ Subgroup.center G) := Fintype.ofFinite _
  have hle : t.card ≤ (Finset.univ : Finset (G ⧸ Subgroup.center G)).card :=
    Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
      (injOn_mk_of_isClique ht.isClique)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index, ht.card_eq] at hle
  omega

end Math0.Erdos1098

#math0_proves Math0.Erdos1098.upper_bound Erdos1098.erdos_1098.variants.upper_bound
