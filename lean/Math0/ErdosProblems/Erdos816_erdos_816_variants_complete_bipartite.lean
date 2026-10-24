/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«816»
import Math0.Audit

/-!
# Erdős Problem 816: the extremal example `K_{n,n+1}`

Erdős Problem 816 (Erdős–Hajnal) asks whether every graph on `2n+1` vertices with `n^2+n+1`
edges contains two vertices of equal degree joined by a path of length `3`. The complete
bipartite graph `K_{n,n+1}` shows that `n^2+n` edges do not suffice; this file proves exactly the
upstream statement `erdos_816.variants.complete_bipartite`: for every `n`, `K_{n,n+1}` has
`n^2+n` edges and has no two distinct vertices of equal degree joined by a path of length `3`.
The edge count is `|Fin n| * |Fin (n+1)| = n(n+1)`. Vertices on the left side have degree
`n+1` and vertices on the right side have degree `n`, so equal-degree vertices lie on the same
side, while any walk of length `3` alternates sides and hence joins opposite sides.
-/

namespace Math0.Erdos816

open SimpleGraph

open scoped Classical in
/-- `K_{n,n+1}` has exactly `n^2 + n` edges. -/
theorem card_edgeFinset (n : ℕ) :
    (completeBipartiteGraph (Fin n) (Fin (n + 1))).edgeFinset.card = n ^ 2 + n := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset, Set.ncard_def,
    encard_edgeSet_completeBipartiteGraph]
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  rw [← Nat.cast_mul, ENat.toNat_natCast]
  ring

open scoped Classical in
/-- In `K_{n,n+1}`, every vertex of the left part `Fin n` has degree `n + 1`. -/
theorem degree_inl (n : ℕ) (a : Fin n) :
    (completeBipartiteGraph (Fin n) (Fin (n + 1))).degree (Sum.inl a) = n + 1 := by
  rw [← card_neighborFinset_eq_degree]
  have : (completeBipartiteGraph (Fin n) (Fin (n + 1))).neighborFinset (Sum.inl a) =
      Finset.univ.map Function.Embedding.inr := by
    ext w; cases w <;> simp
  rw [this]; simp

open scoped Classical in
/-- In `K_{n,n+1}`, every vertex of the right part `Fin (n + 1)` has degree `n`. -/
theorem degree_inr (n : ℕ) (b : Fin (n + 1)) :
    (completeBipartiteGraph (Fin n) (Fin (n + 1))).degree (Sum.inr b) = n := by
  rw [← card_neighborFinset_eq_degree]
  have : (completeBipartiteGraph (Fin n) (Fin (n + 1))).neighborFinset (Sum.inr b) =
      Finset.univ.map Function.Embedding.inl := by
    ext w; cases w <;> simp
  rw [this]; simp

open scoped Classical in
/-- `K_{n,n+1}` contains no two distinct vertices of equal degree joined by a path of length 3:
a walk of length 3 joins opposite sides, and the two sides have different degrees. -/
theorem not_hasEqualDegreePathThree (n : ℕ) :
    ¬ Erdos816.HasEqualDegreePathThree (completeBipartiteGraph (Fin n) (Fin (n + 1))) := by
  rintro ⟨u, v, -, hdeg, p, -, hlen⟩
  match p with
  | .cons h1 (.cons h2 (.cons h3 .nil)) =>
    rename_i x y
    rcases u with a | a <;> rcases v with c | c <;> rcases x with x | x <;>
      rcases y with y | y <;> simp at h1 h2 h3 <;>
      simp only [degree_inl, degree_inr] at hdeg <;> omega

/-- For every `n`, the complete bipartite graph `K_{n,n+1}` on `2n+1` vertices has `n^2 + n`
edges and contains no two vertices of the same degree joined by a path of length `3`. -/
theorem erdos_816_complete_bipartite :
    type_of% @Erdos816.erdos_816.variants.complete_bipartite := by
  intro n
  exact ⟨card_edgeFinset n, not_hasEqualDegreePathThree n⟩

end Math0.Erdos816

#math0_proves Math0.Erdos816.erdos_816_complete_bipartite Erdos816.erdos_816.variants.complete_bipartite
