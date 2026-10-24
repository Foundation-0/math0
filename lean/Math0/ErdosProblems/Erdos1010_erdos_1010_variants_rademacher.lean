/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«1010»
import Math0.Audit

/-!
# Rademacher's theorem on triangles (Erdős Problem 1010, Rademacher variant)

Rademacher (1941, published by Erdős) proved that every graph on `n` vertices with
`⌊n²/4⌋ + 1` edges contains at least `⌊n/2⌋` triangles. We prove exactly the formal statement
`Erdos1010.erdos_1010.variants.rademacher` from formal-conjectures. The proof works with vertex
subsets `S` of a fixed finite graph and proves the stronger "at least `⌊|S|²/4⌋ + 1` edges"
version by strong induction on `|S|`: take a triangle `xyz` (Mantel's theorem, proved by the same
induction); if some edge of it, say `xy`, has `d(x) + d(y) ≤ |S|`, delete `x, y`, apply induction
and add the triangle `xyz`; otherwise every vertex outside `xyz` adjacent to `k` of `x, y, z`
gives at least `k - 1` triangles with an edge of `xyz`, which already yields `⌊|S|/2⌋` triangles.
-/

namespace Math0.Erdos1010

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The adjacency indicator `[v ~ w]`. -/
def ind (v w : V) : ℕ := if G.Adj v w then 1 else 0

/-- The degree of `v` inside the vertex set `S`. -/
def dg (S : Finset V) (v : V) : ℕ := ∑ w ∈ S, ind G v w

/-- The degree sum inside `S`, i.e. twice the number of edges of the induced subgraph. -/
def D (S : Finset V) : ℕ := ∑ v ∈ S, dg G S v

/-- The triangles of `G` contained in `S`. -/
def tri (S : Finset V) : Finset (Finset V) := (G.cliqueFinset 3).filter (· ⊆ S)

omit [Fintype V] [DecidableEq V] in
/-- No loops. -/
lemma ind_self (v : V) : ind G v v = 0 := by simp [ind]

omit [Fintype V] [DecidableEq V] in
/-- The indicator is symmetric. -/
lemma ind_comm (v w : V) : ind G v w = ind G w v := by
  simp only [ind, G.adj_comm]

omit [Fintype V] [DecidableEq V] in
/-- The indicator of an edge is `1`. -/
lemma ind_of_adj {v w : V} (h : G.Adj v w) : ind G v w = 1 := by simp [ind, h]

omit [Fintype V] in
/-- Splitting off one vertex from a degree. -/
lemma dg_erase {S : Finset V} {x : V} (hx : x ∈ S) (v : V) :
    dg G S v = ind G v x + dg G (S.erase x) v := by
  unfold dg; rw [add_sum_erase _ _ hx]

omit [Fintype V] in
/-- Deleting a vertex `x` from `S` lowers the degree sum by `2 d_S(x)`. -/
lemma D_erase {S : Finset V} {x : V} (hx : x ∈ S) :
    D G S = D G (S.erase x) + 2 * dg G S x := by
  unfold D
  rw [← add_sum_erase _ _ hx]
  have h1 : ∀ v ∈ S.erase x, dg G S v = ind G x v + dg G (S.erase x) v := by
    intro v _; rw [dg_erase G hx, ind_comm]
  rw [sum_congr rfl h1, sum_add_distrib]
  have h2 : dg G S x = ∑ v ∈ S.erase x, ind G x v := by
    rw [dg_erase G hx, ind_self, zero_add]; rfl
  omega

omit [Fintype V] [DecidableEq V] in
/-- The degree as the size of a neighbourhood. -/
lemma dg_eq_card (S : Finset V) (v : V) : dg G S v = (S.filter (G.Adj v)).card := by
  rw [card_filter]; rfl

omit [Fintype V] in
/-- Two vertices whose degree sum in `S` exceeds `|S|` have a common neighbour in `S`. -/
lemma exists_common {S : Finset V} {x y : V} (h : S.card < dg G S x + dg G S y) :
    ∃ z ∈ S, G.Adj x z ∧ G.Adj y z := by
  rw [dg_eq_card, dg_eq_card] at h
  have h1 := card_union_add_card_inter (S.filter (G.Adj x)) (S.filter (G.Adj y))
  have h2 : (S.filter (G.Adj x) ∪ S.filter (G.Adj y)).card ≤ S.card :=
    card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have h3 : (S.filter (G.Adj x) ∩ S.filter (G.Adj y)).Nonempty := by
    rw [← card_pos]; omega
  obtain ⟨z, hz⟩ := h3
  simp only [mem_inter, mem_filter] at hz
  exact ⟨z, hz.1.1, hz.1.2, hz.2.2⟩

omit [Fintype V] [DecidableEq V] in
/-- A positive degree sum gives an edge. -/
lemma exists_adj_of_D_pos {S : Finset V} (h : 0 < D G S) : ∃ x ∈ S, ∃ y ∈ S, G.Adj x y := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have : D G S = 0 := by
    unfold D dg
    apply sum_eq_zero
    intro v hv
    apply sum_eq_zero
    intro w hw
    simp [ind, hc v hv w hw]
  omega

omit [Fintype V] in
/-- Deleting both ends of an edge `xy`. -/
lemma D_erase_two {S : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : G.Adj x y) :
    D G S + 2 = D G ((S.erase x).erase y) + 2 * dg G S x + 2 * dg G S y := by
  have hy' : y ∈ S.erase x := mem_erase.2 ⟨(G.ne_of_adj hxy).symm, hy⟩
  rw [D_erase G hx, D_erase G hy', dg_erase G hx y, ind_of_adj G hxy.symm]
  ring

/-- `⌊(M+2)²/4⌋ = ⌊M²/4⌋ + M + 1`. -/
lemma sq_div_four (M : ℕ) : (M + 2) ^ 2 / 4 = M ^ 2 / 4 + M + 1 := by
  have : (M + 2) ^ 2 = M ^ 2 + (M + 1) * 4 := by ring
  rw [this, Nat.add_mul_div_right _ _ (by norm_num)]
  ring

omit [Fintype V] in
/-- Deleting two vertices only shrinks the set. -/
lemma card_erase_two_lt {S : Finset V} {x : V} (hx : x ∈ S) (y : V) :
    ((S.erase x).erase y).card < S.card :=
  lt_of_le_of_lt card_erase_le (card_erase_lt_of_mem hx)

omit [Fintype V] in
/-- The induction step for the edge count: deleting the ends of an edge `xy` with
`d(x) + d(y) ≤ |S|` keeps the hypothesis "at least `⌊|S|²/4⌋ + 1` edges". -/
lemma step_bound {S : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : G.Adj x y)
    (hdeg : dg G S x + dg G S y ≤ S.card) (hD : 2 * (S.card ^ 2 / 4 + 1) ≤ D G S) :
    ((S.erase x).erase y).card + 2 = S.card ∧
    2 * (((S.erase x).erase y).card ^ 2 / 4 + 1) ≤ D G ((S.erase x).erase y) := by
  have hy' : y ∈ S.erase x := mem_erase.2 ⟨(G.ne_of_adj hxy).symm, hy⟩
  have hc : ((S.erase x).erase y).card + 2 = S.card := by
    have := card_erase_add_one hx
    have := card_erase_add_one hy'
    omega
  refine ⟨hc, ?_⟩
  have := D_erase_two G hx hy hxy
  rw [← hc, sq_div_four] at hD
  rw [← hc] at hdeg
  omega

omit [Fintype V] in
/-- Mantel's theorem, in the form needed here: at least `⌊|S|²/4⌋ + 1` edges inside `S` force a
triangle inside `S`. -/
lemma mantel : ∀ (k : ℕ) (S : Finset V), S.card = k → 2 * (S.card ^ 2 / 4 + 1) ≤ D G S →
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk hD
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_adj_of_D_pos G (S := S) (by omega)
  by_cases hdeg : S.card < dg G S x + dg G S y
  · obtain ⟨z, hz, hxz, hyz⟩ := exists_common G hdeg
    exact ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
  · obtain ⟨hc, hD'⟩ := step_bound G hx hy hxy (by omega) hD
    obtain ⟨a, ha, b, hb, c, hc', h1, h2, h3⟩ := ih _ (by omega) _ rfl hD'
    exact ⟨a, mem_of_mem_erase (mem_of_mem_erase ha), b, mem_of_mem_erase (mem_of_mem_erase hb),
      c, mem_of_mem_erase (mem_of_mem_erase hc'), h1, h2, h3⟩

/-- A triangle with vertices in `S` belongs to `tri G S`. -/
lemma mem_tri {S : Finset V} {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    ({a, b, c} : Finset V) ∈ tri G S := by
  unfold tri
  rw [mem_filter, SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
  refine ⟨⟨hab, hac, hbc⟩, ?_⟩
  intro v hv
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

/-- `tri` is monotone. -/
lemma tri_mono {S T : Finset V} (h : S ⊆ T) : tri G S ⊆ tri G T := by
  intro U hU
  simp only [tri, mem_filter] at hU ⊢
  exact ⟨hU.1, hU.2.trans h⟩

/-- Case 1: some edge `xy` of the triangle `xyz` has `d(x) + d(y) ≤ |S|`. -/
lemma case_one {S : Finset V} {x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z)
    (hdeg : dg G S x + dg G S y ≤ S.card) (hD : 2 * (S.card ^ 2 / 4 + 1) ≤ D G S)
    (ih : 2 * (((S.erase x).erase y).card ^ 2 / 4 + 1) ≤ D G ((S.erase x).erase y) →
      ((S.erase x).erase y).card / 2 ≤ (tri G ((S.erase x).erase y)).card) :
    S.card / 2 ≤ (tri G S).card := by
  obtain ⟨hc, hD'⟩ := step_bound G hx hy hxy hdeg hD
  have h1 := ih hD'
  have hsub : insert ({x, y, z} : Finset V) (tri G ((S.erase x).erase y)) ⊆ tri G S := by
    apply insert_subset (mem_tri G hx hy hz hxy hxz hyz)
    exact tri_mono G ((erase_subset _ _).trans (erase_subset _ _))
  have hnot : ({x, y, z} : Finset V) ∉ tri G ((S.erase x).erase y) := by
    intro h
    have := (mem_filter.1 h).2 (mem_insert_self x _)
    simp at this
  have := card_le_card hsub
  rw [card_insert_of_notMem hnot] at this
  omega

/-- Case 2: every edge `uv` of the triangle `xyz` has `d(u) + d(v) > |S|`. -/
lemma case_two {S : Finset V} {x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z)
    (h1 : S.card < dg G S x + dg G S y) (h2 : S.card < dg G S y + dg G S z)
    (h3 : S.card < dg G S x + dg G S z) :
    S.card / 2 ≤ (tri G S).card := by
  have hne1 := G.ne_of_adj hxy
  have hne2 := G.ne_of_adj hxz
  have hne3 := G.ne_of_adj hyz
  have hy' : y ∈ S.erase x := mem_erase.2 ⟨hne1.symm, hy⟩
  have hz' : z ∈ (S.erase x).erase y := mem_erase.2 ⟨hne3.symm, mem_erase.2 ⟨hne2.symm, hz⟩⟩
  have hcard : (((S.erase x).erase y).erase z).card + 3 = S.card := by
    have := card_erase_add_one hx
    have := card_erase_add_one hy'
    have := card_erase_add_one hz'
    omega
  have dx : dg G S x = 2 + dg G (((S.erase x).erase y).erase z) x := by
    rw [dg_erase G hx, dg_erase G hy', dg_erase G hz', ind_self, ind_of_adj G hxy,
      ind_of_adj G hxz]
    ring
  have dy : dg G S y = 2 + dg G (((S.erase x).erase y).erase z) y := by
    rw [dg_erase G hx, dg_erase G hy', dg_erase G hz', ind_self, ind_of_adj G hxy.symm,
      ind_of_adj G hyz]
    ring
  have dz : dg G S z = 2 + dg G (((S.erase x).erase y).erase z) z := by
    rw [dg_erase G hx, dg_erase G hy', dg_erase G hz', ind_self, ind_of_adj G hxz.symm,
      ind_of_adj G hyz.symm]
    ring
  let p : Fin 3 → V := ![x, y, x]
  let r : Fin 3 → V := ![y, z, z]
  have hpr : ∀ i, p i ∈ S ∧ r i ∈ S ∧ G.Adj (p i) (r i) := by
    intro i; fin_cases i <;> simp [p, r, hx, hy, hz, hxy, hxz, hyz]
  have hpr' : ∀ i, (p i = x ∨ p i = y ∨ p i = z) ∧ (r i = x ∨ r i = y ∨ r i = z) := by
    intro i; fin_cases i <;> simp [p, r]
  set R := ((S.erase x).erase y).erase z with hR
  have hRmem : ∀ w ∈ R, w ∈ S ∧ w ≠ x ∧ w ≠ y ∧ w ≠ z := by
    intro w hw; simp only [R, mem_erase] at hw; tauto
  let P := (R ×ˢ (univ : Finset (Fin 3))).filter
    (fun q => G.Adj (p q.2) q.1 ∧ G.Adj (r q.2) q.1)
  let f : V × Fin 3 → Finset V := fun q => {p q.2, r q.2, q.1}
  have hP : dg G R x + dg G R y + dg G R z ≤ P.card + R.card := by
    simp only [P]
    rw [card_filter, sum_product, card_eq_sum_ones R]
    unfold dg
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro w _
    simp only [Fin.sum_univ_three, p, r, ind]
    by_cases ha : G.Adj x w <;> by_cases hb : G.Adj y w <;> by_cases hc : G.Adj z w <;>
      simp [ha, hb, hc]
  have hinj : Set.InjOn f P := by
    rintro ⟨w, i⟩ hq ⟨w', i'⟩ hq' hf
    simp only [P, coe_filter, mem_product] at hq hq'
    obtain ⟨hw, hwx, hwy, hwz⟩ := hRmem w hq.1.1
    simp only [f] at hf
    have ew : w ∈ ({p i', r i', w'} : Finset V) := by rw [← hf]; simp
    simp only [mem_insert, mem_singleton] at ew
    have hww : w = w' := by
      rcases ew with h | h | h
      · rcases (hpr' i').1 with h' | h' | h'
        · exact absurd (h.trans h') hwx
        · exact absurd (h.trans h') hwy
        · exact absurd (h.trans h') hwz
      · rcases (hpr' i').2 with h' | h' | h'
        · exact absurd (h.trans h') hwx
        · exact absurd (h.trans h') hwy
        · exact absurd (h.trans h') hwz
      · exact h
    subst hww
    have ex : x ∈ ({p i, r i, w} : Finset V) ↔ x ∈ ({p i', r i', w} : Finset V) := by rw [hf]
    have ey : y ∈ ({p i, r i, w} : Finset V) ↔ y ∈ ({p i', r i', w} : Finset V) := by rw [hf]
    have ez : z ∈ ({p i, r i, w} : Finset V) ↔ z ∈ ({p i', r i', w} : Finset V) := by rw [hf]
    clear hf hq hq' hpr hpr' hRmem
    fin_cases i <;> fin_cases i' <;>
      first
      | rfl
      | (exfalso
         simp [p, r, hne1, hne2, hne3, hne1.symm, hwx.symm, hwy.symm] at ex ey ez)
  have hsub : insert ({x, y, z} : Finset V) (P.image f) ⊆ tri G S := by
    apply insert_subset (mem_tri G hx hy hz hxy hxz hyz)
    intro T hT
    rw [mem_image] at hT
    obtain ⟨⟨w, i⟩, hq, rfl⟩ := hT
    simp only [P, mem_filter, mem_product] at hq
    exact mem_tri G (hpr i).1 (hpr i).2.1 (hRmem w hq.1.1).1 (hpr i).2.2 hq.2.1 hq.2.2
  have hnot : ({x, y, z} : Finset V) ∉ P.image f := by
    intro h
    rw [mem_image] at h
    obtain ⟨⟨w, i⟩, hq, hf⟩ := h
    simp only [P, mem_filter, mem_product] at hq
    obtain ⟨-, hwx, hwy, hwz⟩ := hRmem w hq.1.1
    have hw : w ∈ ({x, y, z} : Finset V) := hf ▸ (by simp [f])
    simp only [mem_insert, mem_singleton] at hw
    tauto
  have := card_le_card hsub
  rw [card_insert_of_notMem hnot, card_image_of_injOn hinj] at this
  omega

/-- The main induction: at least `⌊|S|²/4⌋ + 1` edges inside `S` give at least `⌊|S|/2⌋`
triangles inside `S`. -/
lemma main : ∀ (k : ℕ) (S : Finset V), S.card = k → 2 * (S.card ^ 2 / 4 + 1) ≤ D G S →
    S.card / 2 ≤ (tri G S).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk hD
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := mantel G _ S rfl hD
  by_cases c1 : dg G S x + dg G S y ≤ S.card
  · exact case_one G hx hy hz hxy hxz hyz c1 hD
      (fun h => ih _ (hk ▸ card_erase_two_lt hx y) _ rfl h)
  by_cases c2 : dg G S y + dg G S z ≤ S.card
  · exact case_one G hy hz hx hyz hxy.symm hxz.symm c2 hD
      (fun h => ih _ (hk ▸ card_erase_two_lt hy z) _ rfl h)
  by_cases c3 : dg G S x + dg G S z ≤ S.card
  · exact case_one G hx hz hy hxz hxy hyz.symm c3 hD
      (fun h => ih _ (hk ▸ card_erase_two_lt hx z) _ rfl h)
  exact case_two G hx hy hz hxy hxz hyz (by omega) (by omega) (by omega)

omit [DecidableEq V] in
/-- The degree sum over all vertices is twice the number of edges. -/
lemma D_univ : D G univ = 2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  unfold D
  apply sum_congr rfl
  intro v _
  rw [dg_eq_card, ← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]

/-- Rademacher's theorem: every graph on `n` vertices with `⌊n²/4⌋ + 1` edges contains at least
`⌊n/2⌋` triangles. -/
theorem erdos_1010_rademacher : type_of% @Erdos1010.erdos_1010.variants.rademacher := by
  intro n G h
  classical
  have key := main G _ (univ : Finset (Fin n)) rfl (by rw [D_univ, h]; simp)
  simpa [tri] using key

end Math0.Erdos1010

#math0_proves Math0.Erdos1010.erdos_1010_rademacher Erdos1010.erdos_1010.variants.rademacher
