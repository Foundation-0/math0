/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«750»
import Math0.Audit

/-!
# Erdős Problem 750: the Erdős–Hajnal bound for `f(m) = c·m`, `c > 1/4`

Erdős Problem 750 asks for graphs of infinite chromatic number in which every `m`-vertex
subgraph has an independent set of size at least `m/2 - f(m)`; Erdős and Hajnal [ErHa67b] did
this for `f(m) = c·m` with any `c > 1/4`. We prove this variant using the shift graph, whose
vertices are pairs `i < j` of naturals with `(i, j)` adjacent to `(j, k)`. It is not
`k`-colourable for any `k`: the sets `T i = {colour (i, j) : j > i}` of colours cannot all differ,
and `T i = T j` with `i < j` makes `(i, j)` share its colour with some neighbour `(j, l)`. For a
finite set `S` of `m` vertices, every `X ⊆ ℕ` gives the independent set
`{(i, j) ∈ S : i ∈ X, j ∉ X}`, and averaging over all subsets `X` of the endpoints shows that one
of them has at least `m/4 ≥ m/2 - c·m` elements.
-/

namespace Math0.Erdos750

open Finset

universe u u_1

/-- Vertices of the shift graph: pairs `(i, j)` of natural numbers with `i < j`, lifted to an
arbitrary universe. -/
abbrev ShiftV : Type u := ULift.{u} {p : ℕ × ℕ // p.1 < p.2}

/-- The shift graph: `(i, j)` is adjacent to `(j, k)`. -/
def shiftGraph : SimpleGraph ShiftV.{u} where
  Adj x y := x.down.1.2 = y.down.1.1 ∨ y.down.1.2 = x.down.1.1
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun x h => by
    have := x.down.2
    rcases h with h | h <;> omega⟩

/-- Adjacency in the shift graph. -/
theorem shiftGraph_adj {x y : ShiftV.{u}} :
    shiftGraph.Adj x y ↔ x.down.1.2 = y.down.1.1 ∨ y.down.1.2 = x.down.1.1 := Iff.rfl

/-- The shift graph is not `k`-colourable for any `k`. -/
theorem shiftGraph_not_colorable (k : ℕ) : ¬ shiftGraph.{u}.Colorable k := by
  rintro ⟨C⟩
  let T : ℕ → Set (Fin k) := fun i => {c | ∃ j, ∃ h : i < j, C ⟨⟨(i, j), h⟩⟩ = c}
  have key : ∀ a b, a < b → T a = T b → False := by
    intro a b hab hT
    have hmem : C ⟨⟨(a, b), hab⟩⟩ ∈ T b := by
      rw [← hT]
      exact ⟨b, hab, rfl⟩
    obtain ⟨l, hbl, hl⟩ := hmem
    exact C.valid (show shiftGraph.Adj (⟨⟨(a, b), hab⟩⟩ : ShiftV) ⟨⟨(b, l), hbl⟩⟩ from
      shiftGraph_adj.mpr (Or.inl rfl)) hl.symm
  obtain ⟨a, b, hab, hT⟩ := Finite.exists_ne_map_eq_of_infinite T
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h hT
  · exact key b a h hT.symm

/-- The shift graph has infinite chromatic number. -/
theorem shiftGraph_chromaticNumber : shiftGraph.{u}.chromaticNumber = ⊤ := by
  by_contra h
  obtain ⟨n, hn⟩ := SimpleGraph.chromaticNumber_ne_top_iff_exists.mp h
  exact shiftGraph_not_colorable n hn

/-- For distinct `a, b ∈ U`, exactly a quarter of the subsets of `U` contain `a` but not `b`. -/
theorem four_mul_card_filter_powerset (U : Finset ℕ) {a b : ℕ} (ha : a ∈ U) (hb : b ∈ U)
    (hab : a ≠ b) :
    4 * (U.powerset.filter (fun X => a ∈ X ∧ b ∉ X)).card = 2 ^ U.card := by
  have h : U.powerset.filter (fun X => a ∈ X ∧ b ∉ X) =
      ((U.erase a).erase b).powerset.image (insert a) := by
    ext X
    simp only [mem_filter, mem_powerset, mem_image]
    constructor
    · rintro ⟨hXU, haX, hbX⟩
      refine ⟨X.erase a, ?_, insert_erase haX⟩
      intro x hx
      rw [mem_erase] at hx
      rw [mem_erase, mem_erase]
      exact ⟨fun h => hbX (h ▸ hx.2), hx.1, hXU hx.2⟩
    · rintro ⟨Y, hY, rfl⟩
      refine ⟨insert_subset ha (hY.trans ((erase_subset _ _).trans (erase_subset _ _))),
        mem_insert_self _ _, ?_⟩
      rw [mem_insert]
      rintro (h | h)
      · exact hab h.symm
      · have := hY h
        simp at this
  have hinj : Set.InjOn (insert a) (((U.erase a).erase b).powerset : Set (Finset ℕ)) := by
    intro Y hY Y' hY' h
    rw [mem_coe, mem_powerset] at hY hY'
    have haY : a ∉ Y := fun h => by
      have := hY h
      simp at this
    have haY' : a ∉ Y' := fun h => by
      have := hY' h
      simp at this
    rw [← erase_insert haY, ← erase_insert haY']
    exact congrArg (fun Z => Z.erase a) h
  rw [h, card_image_of_injOn hinj, card_powerset, card_erase_of_mem (mem_erase.mpr ⟨hab.symm, hb⟩),
    card_erase_of_mem ha]
  have h2 : 1 < U.card := one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  obtain ⟨n, hn⟩ : ∃ n, U.card = n + 2 := ⟨U.card - 2, by omega⟩
  rw [hn, show n + 2 - 1 - 1 = n by omega]
  ring

/-- Averaging over cuts: every finite set `S` of vertices of the shift graph contains at least
`|S| / 4` pairs `(i, j)` with `i ∈ X` and `j ∉ X`, for a suitable `X`. -/
theorem exists_large_cut (S : Finset ShiftV.{u}) :
    ∃ X : Finset ℕ, S.card ≤ 4 * (S.filter (fun p => p.down.1.1 ∈ X ∧ p.down.1.2 ∉ X)).card := by
  set U : Finset ℕ := S.image (fun p => p.down.1.1) ∪ S.image (fun p => p.down.1.2)
  have hsum : ∑ X ∈ U.powerset, S.card ≤
      ∑ X ∈ U.powerset, 4 * (S.filter (fun p => p.down.1.1 ∈ X ∧ p.down.1.2 ∉ X)).card := by
    apply le_of_eq
    calc ∑ X ∈ U.powerset, S.card = ∑ p ∈ S, 2 ^ U.card := by
          rw [sum_const, sum_const, card_powerset, smul_eq_mul, smul_eq_mul, mul_comm]
      _ = ∑ p ∈ S, 4 * (U.powerset.filter (fun X => p.down.1.1 ∈ X ∧ p.down.1.2 ∉ X)).card := by
          refine sum_congr rfl (fun p hp => ?_)
          exact (four_mul_card_filter_powerset U (mem_union_left _ (mem_image_of_mem _ hp))
            (mem_union_right _ (mem_image_of_mem _ hp)) (ne_of_lt p.down.2)).symm
      _ = ∑ p ∈ S, ∑ X ∈ U.powerset,
            4 * (if p.down.1.1 ∈ X ∧ p.down.1.2 ∉ X then 1 else 0) := by
          simp only [card_filter, mul_sum]
      _ = ∑ X ∈ U.powerset, ∑ p ∈ S,
            4 * (if p.down.1.1 ∈ X ∧ p.down.1.2 ∉ X then 1 else 0) := sum_comm
      _ = ∑ X ∈ U.powerset, 4 * (S.filter (fun p => p.down.1.1 ∈ X ∧ p.down.1.2 ∉ X)).card := by
          simp only [card_filter, mul_sum]
  obtain ⟨X, -, hX⟩ := exists_le_of_sum_le ⟨∅, empty_mem_powerset _⟩ hsum
  exact ⟨X, hX⟩

/-- Erdős–Hajnal: for every `c > 1/4` there is a graph of infinite chromatic number in which every
set of `m ≥ 1` vertices contains an independent set of size at least `m/2 - c·m`. -/
theorem c_gt_quarter : type_of% @Erdos750.erdos_750.variants.c_gt_quarter.{u_1} := by
  intro c hc
  refine ⟨ShiftV.{u_1}, shiftGraph, shiftGraph_chromaticNumber, ?_⟩
  intro m S hm hS
  have hfin : S.Finite := Set.finite_of_ncard_pos (hS ▸ hm)
  obtain ⟨X, hX⟩ := exists_large_cut hfin.toFinset
  refine ⟨{p | p ∈ S ∧ p.down.1.1 ∈ X ∧ p.down.1.2 ∉ X}, fun p hp => hp.1, ?_, ?_⟩
  · intro p hp q hq _ hadj
    rcases shiftGraph_adj.mp hadj with h | h
    · exact hp.2.2 (by rw [h]; exact hq.2.1)
    · exact hq.2.2 (by rw [h]; exact hp.2.1)
  · have hcard : ({p | p ∈ S ∧ p.down.1.1 ∈ X ∧ p.down.1.2 ∉ X} : Set ShiftV).ncard =
        (hfin.toFinset.filter (fun p => p.down.1.1 ∈ X ∧ p.down.1.2 ∉ X)).card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext p
      simp
    have hScard : hfin.toFinset.card = m := by rw [← hS, Set.ncard_eq_toFinset_card S hfin]
    rw [hcard]
    set k := (hfin.toFinset.filter (fun p => p.down.1.1 ∈ X ∧ p.down.1.2 ∉ X)).card
    have h4 : (m : NNReal) ≤ 4 * k := by rw [← hScard]; exact_mod_cast hX
    calc (m : NNReal) / 2 - c * m ≤ m / 2 - 1 / 4 * m :=
          tsub_le_tsub_left (mul_le_mul_of_nonneg_right hc.le (by positivity)) _
      _ ≤ k := by
          rw [tsub_le_iff_right, ← NNReal.coe_le_coe]
          rw [← NNReal.coe_le_coe] at h4
          push_cast at h4 ⊢
          linarith

end Math0.Erdos750

#math0_proves Math0.Erdos750.c_gt_quarter Erdos750.erdos_750.variants.c_gt_quarter
