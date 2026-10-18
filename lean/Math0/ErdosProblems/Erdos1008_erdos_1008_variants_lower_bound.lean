/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1008»
import Math0.Audit

/-!
# Erdős Problem 1008: the trivial `√m` lower bound for `C₄`-free subgraphs

Erdős Problem 1008 asks whether every graph with `m` edges has a `C₄`-free subgraph with
`≫ m^{2/3}` edges; in [Er71] Erdős remarks that `≫ m^{1/2}` is trivial. This file proves exactly
the upstream statement `erdos_1008.variants.lower_bound`, with the constant `c = 1/2`: every finite
graph `G` with `m` edges has a `C₄`-free subgraph with at least `√m / 2` edges.
Let `Δ` be the maximum degree and `M` a maximum matching. Every edge of `G` meets an edge of `M`
(otherwise `M` could be enlarged), and at most `2Δ` edges meet a given edge, so `m ≤ 2|M|Δ`;
hence `max(Δ, |M|) ≥ √(m/2) ≥ √m/2`. Both the star at a maximum-degree vertex (all its edges
share the centre, while a `C₄` has two disjoint edges) and the matching (all degrees at most one,
while `C₄` is `2`-regular) are `C₄`-free.
-/

open SimpleGraph

namespace Math0.Erdos1008

/-- The graph spanned by a finset `s` of edges of `G` is a subgraph of `G` with exactly
`s.card` edges. -/
theorem fromEdgeSet_finset {V : Type} (G : SimpleGraph V) [Fintype G.edgeSet]
    (s : Finset (Sym2 V)) (hs : s ⊆ G.edgeFinset) :
    fromEdgeSet (s : Set (Sym2 V)) ≤ G ∧
      (fromEdgeSet (s : Set (Sym2 V))).edgeSet.ncard = s.card := by
  have hs' : ∀ e ∈ s, e ∈ G.edgeSet := fun e he => by simpa using hs he
  refine ⟨fun x y h => ?_, ?_⟩
  · rw [fromEdgeSet_adj] at h
    exact (mem_edgeSet G).1 (hs' _ h.1)
  · rw [edgeSet_fromEdgeSet]
    have : (s : Set (Sym2 V)) \ Sym2.diagSet = s := by
      ext e
      constructor
      · exact fun h => h.1
      · intro he
        exact ⟨he, fun hd => G.not_isDiag_of_mem_edgeSet (hs' _ he) hd⟩
    rw [this, Set.ncard_coe_finset]

/-- A finset of edges is a matching when any two of its edges sharing a vertex are equal. -/
def IsMatch {V : Type} (M : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, ∀ x, x ∈ e → x ∈ e' → e = e'

/-- Every finite graph has a matching `M` (a maximum one) with `|E(G)| ≤ 2 |M| Δ(G)`: by
maximality every edge meets an edge of `M`, and each edge of `M` meets at most `2 Δ(G)` edges. -/
theorem exists_matching {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∃ M : Finset (Sym2 V), M ⊆ G.edgeFinset ∧ IsMatch M ∧
      G.edgeFinset.card ≤ 2 * M.card * G.maxDegree := by
  classical
  set S := G.edgeFinset.powerset.filter (fun M => IsMatch M) with hS
  have hne : S.Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by simp [IsMatch]⟩⟩
  obtain ⟨M, hMS, hmax⟩ := S.exists_max_image Finset.card hne
  simp only [hS, Finset.mem_filter, Finset.mem_powerset] at hMS
  obtain ⟨hMsub, hMm⟩ := hMS
  refine ⟨M, hMsub, hMm, ?_⟩
  -- every edge meets an edge of M
  have hcover : ∀ e ∈ G.edgeFinset, ∃ f ∈ M, ∃ x, x ∈ f ∧ x ∈ e := by
    intro e he
    by_contra hcon
    push Not at hcon
    have heM : e ∉ M := by
      intro heM
      induction e using Sym2.ind with
      | _ a b => exact hcon _ heM a (Sym2.mem_mk_left a b) (Sym2.mem_mk_left a b)
    have hins : insert e M ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset he hMsub, ?_⟩
      intro e1 he1 e2 he2 x hx1 hx2
      rw [Finset.mem_insert] at he1 he2
      rcases he1 with rfl | he1 <;> rcases he2 with rfl | he2
      · rfl
      · exact absurd hx1 (hcon _ he2 x hx2)
      · exact absurd hx2 (hcon _ he1 x hx1)
      · exact hMm _ he1 _ he2 x hx1 hx2
    have := hmax _ hins
    rw [Finset.card_insert_of_notMem heM] at this
    omega
  have hsub : G.edgeFinset ⊆ M.biUnion
      (fun f => G.edgeFinset.filter (fun e => ∃ x, x ∈ f ∧ x ∈ e)) := by
    intro e he
    obtain ⟨f, hf, hx⟩ := hcover e he
    exact Finset.mem_biUnion.2 ⟨f, hf, Finset.mem_filter.2 ⟨he, hx⟩⟩
  have hbound : ∀ f ∈ M,
      (G.edgeFinset.filter (fun e => ∃ x, x ∈ f ∧ x ∈ e)).card ≤ 2 * G.maxDegree := by
    intro f _
    induction f using Sym2.ind with
    | _ a b =>
    have : G.edgeFinset.filter (fun e => ∃ x, x ∈ s(a, b) ∧ x ∈ e) ⊆
        G.incidenceFinset a ∪ G.incidenceFinset b := by
      intro e he
      simp only [Finset.mem_filter, Sym2.mem_iff] at he
      obtain ⟨he, x, hx, hxe⟩ := he
      rw [Finset.mem_union, mem_incidenceFinset, mem_incidenceFinset]
      rw [mem_edgeFinset] at he
      rcases hx with rfl | rfl
      · exact Or.inl ⟨he, hxe⟩
      · exact Or.inr ⟨he, hxe⟩
    calc _ ≤ (G.incidenceFinset a ∪ G.incidenceFinset b).card := Finset.card_le_card this
      _ ≤ (G.incidenceFinset a).card + (G.incidenceFinset b).card := Finset.card_union_le _ _
      _ = G.degree a + G.degree b := by
          rw [card_incidenceFinset_eq_degree, card_incidenceFinset_eq_degree]
      _ ≤ G.maxDegree + G.maxDegree := add_le_add (G.degree_le_maxDegree a)
          (G.degree_le_maxDegree b)
      _ = 2 * G.maxDegree := by ring
  calc G.edgeFinset.card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ f ∈ M, (G.edgeFinset.filter (fun e => ∃ x, x ∈ f ∧ x ∈ e)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ f ∈ M, 2 * G.maxDegree := Finset.sum_le_sum hbound
    _ = 2 * M.card * G.maxDegree := by rw [Finset.sum_const, smul_eq_mul]; ring

/-- A copy of `C₄` in `H` yields four distinct vertices `a, b, c, d` with `a ~ b ~ c ~ d`. -/
theorem exists_c4 {V : Type} {H : SimpleGraph V} (h : cycleGraph 4 ⊑ H) :
    ∃ a b c d : V, H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨f⟩ := h
  refine ⟨f 0, f 1, f 2, f 3, f.toHom.map_adj (by decide), f.toHom.map_adj (by decide),
    f.toHom.map_adj (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  exact f.injective.ne (by decide)

/-- A graph all of whose edges contain a fixed vertex `v` (a star) is `C₄`-free. -/
theorem free_of_star {V : Type} {H : SimpleGraph V} (v : V)
    (hv : ∀ x y, H.Adj x y → x = v ∨ y = v) : (cycleGraph 4).Free H := by
  intro h
  obtain ⟨a, b, c, d, hab, -, hcd, h1, h2, h3, h4, h5, h6⟩ := exists_c4 h
  rcases hv _ _ hab with rfl | rfl <;> rcases hv _ _ hcd with rfl | rfl <;> simp_all

/-- A graph in which every vertex has at most one neighbour (a matching) is `C₄`-free. -/
theorem free_of_matching {V : Type} {H : SimpleGraph V}
    (hv : ∀ x y z, H.Adj x y → H.Adj x z → y = z) : (cycleGraph 4).Free H := by
  intro h
  obtain ⟨a, b, c, d, hab, hbc, -, -, h2, -⟩ := exists_c4 h
  exact h2 (hv _ _ _ hab.symm hbc)


/-- If `m ≤ 2ab` and `a, b ≤ k` then `√m / 2 ≤ k`. -/
theorem real_bound (m a b k : ℕ) (hm : m ≤ 2 * a * b) (ha : a ≤ k) (hb : b ≤ k) :
    (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) ≤ k := by
  rw [← Real.sqrt_eq_rpow]
  have h1 : (m : ℝ) ≤ (2 * k : ℝ) ^ 2 := by
    have : m ≤ 4 * k * k := by
      calc m ≤ 2 * a * b := hm
        _ ≤ 2 * k * k := by gcongr
        _ ≤ 4 * k * k := by gcongr; norm_num
    have : (m : ℝ) ≤ 4 * k * k := by exact_mod_cast this
    nlinarith
  have h2 : Real.sqrt m ≤ 2 * k := Real.sqrt_le_iff.2 ⟨by positivity, h1⟩
  linarith

/-- Every finite graph with `m` edges has a `C₄`-free subgraph with at least `(1/2) m^{1/2}`
edges; so the upstream statement holds with `c = 1/2`. -/
theorem lower_bound : type_of% @Erdos1008.erdos_1008.variants.lower_bound := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro V _ G
  classical
  obtain ⟨M, hMsub, hMm, hcard⟩ := exists_matching G
  have hm : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
  rw [hm]
  by_cases hle : G.maxDegree ≤ M.card
  · obtain ⟨hH, hHc⟩ := fromEdgeSet_finset G M hMsub
    refine ⟨_, hH, ?_, ?_⟩
    · apply free_of_matching
      intro x y z hxy hxz
      rw [fromEdgeSet_adj] at hxy hxz
      have := hMm _ hxy.1 _ hxz.1 x (Sym2.mem_mk_left x y) (Sym2.mem_mk_left x z)
      exact Sym2.congr_right.1 this
    · rw [hHc]
      exact real_bound _ _ _ _ hcard le_rfl hle
  · have hpos : 0 < G.maxDegree := by omega
    have : Nonempty V := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      rw [maxDegree_of_subsingleton] at hpos
      omega
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    have hsub : G.incidenceFinset v ⊆ G.edgeFinset := by
      intro e he
      rw [mem_incidenceFinset] at he
      rw [mem_edgeFinset]
      exact he.1
    obtain ⟨hH, hHc⟩ := fromEdgeSet_finset G _ hsub
    refine ⟨_, hH, ?_, ?_⟩
    · apply free_of_star v
      intro x y hxy
      rw [fromEdgeSet_adj, Finset.mem_coe, mem_incidenceFinset] at hxy
      rcases (Sym2.mem_iff.1 hxy.1.2) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rw [hHc, card_incidenceFinset_eq_degree, ← hv]
      exact real_bound _ _ _ _ hcard (by omega) le_rfl

end Math0.Erdos1008

#math0_proves Math0.Erdos1008.lower_bound Erdos1008.erdos_1008.variants.lower_bound
