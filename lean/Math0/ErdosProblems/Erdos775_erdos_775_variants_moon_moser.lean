/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«775»
import Math0.Audit

/-!
# Erdős Problem 775 (Moon–Moser): at most `n - log₂ n + O(1)` clique sizes

Moon and Moser (1965) showed that a graph on `n` vertices has maximal cliques of at most
`n - log₂ n + O(1)` different sizes; together with Spencer's construction this settles the graph
case of Erdős Problem 775 (erdosproblems.com/775). We prove the upstream statement with the
explicit constant `C = 1`, for every `n` (including `n = 0`). Fix a maximum clique `K` of size
`ω`. Every maximal clique has size in `[1, ω]`, so there are at most `ω` sizes; and a maximal
clique `S` is determined by `S \ K` (two maximal cliques agreeing outside `K` have a union that
is a clique), so there are at most `2 ^ (n - ω)` maximal cliques. With `L = ⌊log₂ n⌋`, either
`ω ≤ n - L`, or `2 ^ (n - ω) ≤ 2 ^ (L - 1) ≤ n - L`; and `log₂ n < L + 1`.
-/

open Finset

namespace Math0.Erdos775

/-- The predicate "`S` is a maximal clique of `G`" on finsets. -/
abbrev IsMaxCl {V : Type} (G : SimpleGraph V) (S : Finset V) : Prop :=
  Maximal (fun T : Finset V => G.IsClique (T : Set V)) S

/-- Two maximal cliques that agree outside a clique `K` are equal: their union is a clique. -/
theorem eq_of_sdiff_eq {V : Type} [DecidableEq V] {G : SimpleGraph V} {K S S' : Finset V}
    (hK : G.IsClique (K : Set V)) (hS : IsMaxCl G S) (hS' : IsMaxCl G S')
    (h : S \ K = S' \ K) : S = S' := by
  have memK : ∀ x, x ∈ S → x ∉ S' → x ∈ K := by
    intro x hx hx'
    by_contra hxK
    have : x ∈ S \ K := mem_sdiff.2 ⟨hx, hxK⟩
    rw [h] at this
    exact hx' (mem_sdiff.1 this).1
  have memK' : ∀ x, x ∈ S' → x ∉ S → x ∈ K := by
    intro x hx hx'
    by_contra hxK
    have : x ∈ S' \ K := mem_sdiff.2 ⟨hx, hxK⟩
    rw [← h] at this
    exact hx' (mem_sdiff.1 this).1
  have hU : G.IsClique ((S ∪ S' : Finset V) : Set V) := by
    intro a ha b hb hab
    simp only [coe_union, Set.mem_union, mem_coe] at ha hb
    by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S
    · exact hS.prop haS hbS hab
    · have hb' : b ∈ S' := hb.resolve_left hbS
      by_cases haS' : a ∈ S'
      · exact hS'.prop haS' hb' hab
      · exact hK (memK a haS haS') (memK' b hb' hbS) hab
    · have ha' : a ∈ S' := ha.resolve_left haS
      by_cases hbS' : b ∈ S'
      · exact hS'.prop ha' hbS' hab
      · exact hK (memK' a ha' haS) (memK b hbS hbS') hab
    · exact hS'.prop (ha.resolve_left haS) (hb.resolve_left hbS) hab
  have e1 : S = S ∪ S' := hS.eq_of_le hU subset_union_left
  have e2 : S' = S ∪ S' := hS'.eq_of_le hU subset_union_right
  exact e1.trans e2.symm

/-- The number of clique sizes is at most `2 ^ (|V| - |K|)` for any clique `K`, since a maximal
clique `S` is determined by `S \ K ⊆ V \ K`. -/
theorem ncard_cliqueSizes_le_two_pow {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {K : Finset V} (hK : G.IsClique (K : Set V)) :
    G.cliqueSizes.ncard ≤ 2 ^ (Fintype.card V - K.card) := by
  classical
  set M : Finset (Finset V) := univ.filter (fun S => IsMaxCl G S) with hM
  have hsub : G.cliqueSizes ⊆ ((M.image Finset.card : Finset ℕ) : Set ℕ) := by
    rintro k ⟨S, hS, rfl⟩
    simp only [coe_image, Set.mem_image, mem_coe]
    exact ⟨S, by simpa [hM] using hS, rfl⟩
  calc G.cliqueSizes.ncard ≤ ((M.image Finset.card : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (M.image Finset.card).card := Set.ncard_coe_finset _
    _ ≤ M.card := card_image_le
    _ ≤ ((univ \ K).powerset).card := by
        apply Finset.card_le_card_of_injOn (fun S => S \ K)
        · intro S _
          simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
          exact sdiff_subset_sdiff (subset_univ _) le_rfl
        · intro S hS S' hS' h
          simp only [hM, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS hS'
          exact eq_of_sdiff_eq hK hS hS' h
    _ = 2 ^ (Fintype.card V - K.card) := by
        rw [card_powerset, card_univ_sdiff]

/-- In a nonempty finite graph, every clique size lies in `[1, |K|]` for a maximum clique `K`. -/
theorem ncard_cliqueSizes_le_card {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) {K : Finset V} (hK : G.IsMaximumClique K) :
    G.cliqueSizes.ncard ≤ K.card := by
  have hsub : G.cliqueSizes ⊆ ((Finset.Icc 1 K.card : Finset ℕ) : Set ℕ) := by
    rintro k ⟨S, hS, rfl⟩
    simp only [coe_Icc, Set.mem_Icc]
    refine ⟨?_, hK.maximum S hS.prop⟩
    rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero]
    rintro rfl
    obtain ⟨v⟩ := ‹Nonempty V›
    have h1 : G.IsClique (({v} : Finset V) : Set V) := by simp
    have := hS.eq_of_le h1 (empty_subset _)
    simp at this
  calc G.cliqueSizes.ncard ≤ ((Finset.Icc 1 K.card : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = K.card := by rw [Set.ncard_coe_finset]; simp

/-- `log₂ n < ⌊log₂ n⌋ + 1`. -/
theorem logb_lt_log_add_one (n : ℕ) : Real.logb 2 n < (Nat.log 2 n : ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast hn)]
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    have h2 : ((n : ℕ) : ℝ) < ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ) := by exact_mod_cast this
    have e : ((Nat.log 2 n : ℝ) + 1) = ((Nat.log 2 n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e, Real.rpow_natCast]
    exact_mod_cast h2

/-- The arithmetic core: if `t ≤ k` and `t ≤ 2^(n-k)` with `k ≤ n`, then
`t ≤ n - ⌊log₂ n⌋`. -/
theorem nat_bound (n k t : ℕ) (hn : 1 ≤ n) (h1 : t ≤ k) (h2 : t ≤ 2 ^ (n - k)) (hk : k ≤ n) :
    t + Nat.log 2 n ≤ n := by
  set L := Nat.log 2 n with hL
  have hpow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  by_cases hc : k + L ≤ n
  · omega
  · have hL1 : 1 ≤ L := by omega
    have h3 : 2 ^ (n - k) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : L - 1 < 2 ^ (L - 1) := Nat.lt_two_pow_self
    have h5 : 2 ^ L = 2 ^ (L - 1) + 2 ^ (L - 1) := by
      rw [← two_mul, ← pow_succ']; congr 1; omega
    omega

/-- Moon–Moser with `C = 1`: every graph on `n` vertices has at most `n - log₂ n + 1`
clique sizes. -/
theorem main_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    (G.cliqueSizes.ncard : ℝ) ≤ (n : ℝ) - Real.logb 2 (n : ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hsub : G.cliqueSizes ⊆ {0} := by
      rintro k ⟨S, _, rfl⟩
      simp [Finset.eq_empty_of_isEmpty S]
    have := Set.ncard_le_ncard hsub (Set.finite_singleton 0)
    simp only [Set.ncard_singleton] at this
    simp only [CharP.cast_eq_zero, Real.logb_zero, sub_zero, zero_add]
    exact_mod_cast this
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨K, hK⟩ := G.maximumClique_exists
    have h1 := ncard_cliqueSizes_le_card G hK
    have h2 := ncard_cliqueSizes_le_two_pow G hK.isClique
    have hk : K.card ≤ n := by simpa using card_le_univ K
    rw [Fintype.card_fin] at h2
    have key := nat_bound n K.card _ hn h1 h2 hk
    have hlog := logb_lt_log_add_one n
    have key' : ((G.cliqueSizes.ncard : ℕ) : ℝ) + (Nat.log 2 n : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast key
    linarith

/-- **Moon–Moser.** There is a constant `C` (namely `C = 1`) such that every graph on `n`
vertices has at most `n - log₂ n + C` distinct sizes of maximal cliques. -/
theorem erdos_775_moon_moser : type_of% @Erdos775.erdos_775.variants.moon_moser :=
  ⟨1, main_bound⟩

end Math0.Erdos775

#math0_proves Math0.Erdos775.erdos_775_moon_moser Erdos775.erdos_775.variants.moon_moser
