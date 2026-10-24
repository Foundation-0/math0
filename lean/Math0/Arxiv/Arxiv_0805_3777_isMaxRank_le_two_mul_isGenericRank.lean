/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Arxiv.«0805.3777».TensorRank
import Math0.Audit

/-!
# Maximal rank is at most twice the generic rank (Blekherman–Teitler)

Blekherman and Teitler [BT15, Theorem 1] proved that the maximal rank of tensors of a given
format is at most twice the generic rank. We prove exactly the formal statement
`Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank` from formal-conjectures, where the generic
rank `r` is witnessed by an open dense set `U` of tensors of rank `r`. Given any tensor `T`, the
set `T - U` is open and nonempty, so it meets the dense set `U`; this gives `u ∈ U` with
`T - u ∈ U`, and `T = u + (T - u)` is a sum of two tensors of rank `r`, so `cprank T ≤ 2r`.
-/

open Arxiv.«0805.3777»

namespace Math0.Arxiv.«0805.3777»

/-- The map `x ↦ T - x` on complex holors is continuous for the product topology. -/
lemma continuous_sub_left {ds : List ℕ} (T : Holor ℂ ds) :
    Continuous (fun x : Holor ℂ ds => T - x) := by
  have h : Continuous (fun x : HolorIndex ds → ℂ => (show HolorIndex ds → ℂ from T) - x) :=
    continuous_const.sub continuous_id
  exact h

/-- A holor of CP rank at most `n` (in the sense of `Holor.CPRankMax`) has `cprank ≤ n`. -/
lemma cprank_le_of_cprankMax {ds : List ℕ} {n : ℕ} {x : Holor ℂ ds}
    (h : Holor.CPRankMax n x) : x.cprank ≤ n := by
  classical
  unfold Holor.cprank
  exact Nat.find_min' _ h

/-- Every holor satisfies `CPRankMax (cprank x) x`. -/
lemma cprankMax_cprank {ds : List ℕ} (x : Holor ℂ ds) : Holor.CPRankMax x.cprank x := by
  classical
  unfold Holor.cprank
  exact Nat.find_spec (p := fun n => Holor.CPRankMax n x) _

/-- The maximal rank is at most twice the generic rank [BT15, Theorem 1]. -/
theorem isMaxRank_le_two_mul_isGenericRank :
    type_of% @Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank := by
  intro ds r R hr hR
  obtain ⟨U, hUo, hUd, hUr⟩ := hr
  obtain ⟨T, hT⟩ := hR.1
  subst hT
  obtain ⟨u₀, hu₀⟩ := hUd.nonempty
  have hV : IsOpen ((fun x : Holor ℂ ds => T - x) ⁻¹' U) :=
    hUo.preimage (continuous_sub_left T)
  have hVne : ((fun x : Holor ℂ ds => T - x) ⁻¹' U).Nonempty :=
    ⟨T - u₀, by simpa using hu₀⟩
  obtain ⟨u, huV, huU⟩ := hUd.inter_open_nonempty _ hV hVne
  have h1 : Holor.CPRankMax r u := hUr u huU ▸ cprankMax_cprank u
  have h2 : Holor.CPRankMax r (T - u) := hUr (T - u) huV ▸ cprankMax_cprank (T - u)
  have h3 := Holor.cprankMax_add h1 h2
  rw [add_sub_cancel] at h3
  have := cprank_le_of_cprankMax h3
  show T.cprank ≤ 2 * r
  omega

end Math0.Arxiv.«0805.3777»

#math0_proves Math0.Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank
