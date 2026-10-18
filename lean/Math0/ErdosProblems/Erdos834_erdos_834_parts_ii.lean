/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«834»
import Math0.Audit

/-!
# A 3-critical 3-uniform hypergraph of minimum degree 7 (Erdős Problem 834, part ii)

Erdős and Lovász asked whether there is a 3-critical 3-uniform hypergraph in which every vertex
has degree at least 7, where (in the chromatic formulation) 3-critical means that the weak
chromatic number is 3 and deleting any edge, or any vertex together with its incident edges,
leaves a 2-colorable hypergraph. Li [Li25] answered this positively with a 22-edge example on 9
vertices. We prove exactly the formal statement `Erdos834.erdos_834.parts.ii` with a different,
21-edge, 7-regular example on `Fin 9` found by a SAT search. Uniformity, the degrees and an
explicit proper 3-coloring are checked by `decide`; non-2-colorability is checked by kernel
`decide` over all `2^9` maps `Fin 9 → Fin 2`; and for every edge and every vertex we exhibit an
explicit proper 2-coloring of the remaining hypergraph.
-/

namespace Math0.Erdos834

/-- The witness: a 7-regular 3-uniform hypergraph with 21 edges on the vertex set `Fin 9`. -/
def H : Finset (Finset (Fin 9)) :=
  {{0, 1, 4}, {0, 1, 5}, {0, 1, 6}, {0, 2, 6}, {0, 4, 6}, {0, 5, 6}, {0, 5, 8}, {1, 3, 5},
   {1, 3, 8}, {1, 4, 6}, {1, 5, 8}, {2, 3, 4}, {2, 3, 7}, {2, 4, 6}, {2, 4, 7}, {2, 6, 7},
   {2, 7, 8}, {3, 4, 7}, {3, 5, 8}, {3, 7, 8}, {5, 7, 8}}

/-- Every edge of `H` has exactly three vertices. -/
lemma H_uniform : H.IsUniform 3 := by
  unfold Finset.IsUniform; decide +kernel

/-- Every vertex of `H` lies in at least (in fact exactly) seven edges. -/
lemma H_deg : ∀ v : Fin 9, 7 ≤ H.hypergraphDegree v := by
  unfold Finset.hypergraphDegree; decide +kernel

/-- `H` has a proper 3-coloring, with color classes `{0,1,2,3}`, `{4,5,6,7}`, `{8}`. -/
lemma H_col3 : H.HypergraphColorable 3 :=
  ⟨![0, 0, 0, 0, 1, 1, 1, 1, 2], by unfold Finset.IsProperHypergraphColoring; decide +kernel⟩

/-- `H` has no proper 2-coloring (checked over all `2^9` maps `Fin 9 → Fin 2`). -/
lemma H_not2 : ∀ c : Fin 9 → Fin 2, ¬ H.IsProperHypergraphColoring c := by
  unfold Finset.IsProperHypergraphColoring; decide +kernel

/-- `H` is not colorable with fewer than three colors. -/
lemma H_not_lt3 : ∀ j < 3, ¬ H.HypergraphColorable j := by
  intro j hj ⟨c, hc⟩
  interval_cases j
  · exact Fin.elim0 (c 0)
  · obtain ⟨x, -, y, -, hxy⟩ := hc {0, 1, 4} (by decide +kernel)
    exact hxy (Subsingleton.elim _ _)
  · exact H_not2 c hc

/-- For each edge `e` of `H`, a 2-coloring under which `e` is the only monochromatic edge. -/
def edgeColoring (e : Finset (Fin 9)) : Fin 9 → Fin 2 :=
  if e = {0, 1, 4} then ![0, 0, 0, 1, 0, 1, 1, 1, 0]
  else if e = {0, 1, 5} then ![0, 0, 0, 1, 1, 0, 1, 0, 1]
  else if e = {0, 1, 6} then ![0, 0, 1, 0, 1, 1, 0, 0, 1]
  else if e = {0, 2, 6} then ![0, 1, 0, 0, 1, 1, 0, 1, 0]
  else if e = {0, 4, 6} then ![0, 1, 1, 0, 0, 1, 0, 1, 0]
  else if e = {0, 5, 6} then ![0, 1, 1, 0, 1, 0, 0, 0, 1]
  else if e = {0, 5, 8} then ![0, 1, 0, 1, 0, 0, 1, 1, 0]
  else if e = {1, 3, 5} then ![0, 1, 0, 1, 0, 1, 1, 1, 0]
  else if e = {1, 3, 8} then ![0, 0, 0, 0, 1, 1, 1, 1, 0]
  else if e = {1, 4, 6} then ![0, 1, 0, 0, 1, 0, 1, 1, 1]
  else if e = {1, 5, 8} then ![0, 1, 1, 0, 1, 1, 0, 0, 1]
  else if e = {2, 3, 4} then ![0, 1, 0, 0, 0, 0, 1, 1, 1]
  else if e = {2, 3, 7} then ![0, 0, 0, 0, 1, 1, 1, 0, 1]
  else if e = {2, 4, 6} then ![0, 0, 1, 0, 1, 1, 1, 0, 1]
  else if e = {2, 4, 7} then ![0, 1, 1, 0, 1, 1, 0, 1, 0]
  else if e = {2, 6, 7} then ![0, 1, 1, 0, 0, 1, 1, 1, 0]
  else if e = {2, 7, 8} then ![0, 0, 0, 1, 1, 1, 1, 0, 0]
  else if e = {3, 4, 7} then ![0, 0, 0, 1, 1, 1, 1, 1, 0]
  else if e = {3, 5, 8} then ![0, 0, 0, 1, 1, 1, 1, 0, 1]
  else if e = {3, 7, 8} then ![0, 1, 1, 0, 1, 1, 0, 0, 0]
  else ![0, 0, 0, 0, 1, 1, 1, 1, 1]  -- the edge {5, 7, 8}

/-- `edgeColoring e` properly 2-colors `H` with the edge `e` deleted. -/
lemma edgeColoring_proper :
    ∀ e ∈ H, (H.erase e).IsProperHypergraphColoring (edgeColoring e) := by
  unfold Finset.IsProperHypergraphColoring; decide +kernel

/-- Deleting any single edge of `H` leaves a 2-colorable hypergraph. -/
lemma H_erase : ∀ e ∈ H, (H.erase e).HypergraphColorable 2 :=
  fun e he ↦ ⟨edgeColoring e, edgeColoring_proper e he⟩

/-- For each vertex `v`, a 2-coloring of `H` with all edges through `v` deleted. -/
def vertexColoring : Fin 9 → Fin 9 → Fin 2 :=
  ![![0, 0, 0, 1, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 1],
    ![0, 0, 0, 1, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 1],
    ![0, 0, 1, 0, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 1, 0]]

/-- `vertexColoring v` properly 2-colors the edges of `H` avoiding `v`. -/
lemma vertexColoring_proper :
    ∀ v : Fin 9, (H.filter (fun e ↦ v ∉ e)).IsProperHypergraphColoring (vertexColoring v) := by
  unfold Finset.IsProperHypergraphColoring; decide +kernel

/-- Deleting any single vertex of `H` (with its incident edges) leaves a 2-colorable
hypergraph. -/
lemma H_vertex : ∀ v : Fin 9, (H.filter (fun e ↦ v ∉ e)).HypergraphColorable 2 :=
  fun v ↦ ⟨vertexColoring v, vertexColoring_proper v⟩

/-- **Erdős Problem 834 (ii).** There is a 3-uniform hypergraph with weak chromatic number 3
such that deleting any edge, or any vertex with its incident edges, makes it 2-colorable, and in
which every vertex has degree at least 7. -/
theorem erdos_834_parts_ii : type_of% @Erdos834.erdos_834.parts.ii :=
  ⟨9, H, H_uniform, ⟨H_col3, H_not_lt3⟩, H_erase, H_vertex, H_deg⟩

end Math0.Erdos834

#math0_proves Math0.Erdos834.erdos_834_parts_ii Erdos834.erdos_834.parts.ii
