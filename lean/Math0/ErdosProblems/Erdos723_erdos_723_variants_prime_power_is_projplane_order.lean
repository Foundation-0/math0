/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«723»
import Math0.Audit

/-!
# Projective planes of every prime-power order (Erdős Problem 723, existence variant)

Erdős Problem 723 (the prime power conjecture) asks whether every finite projective plane has
prime-power order. The converse direction, recorded upstream as
`Erdos723.erdos_723.variants.prime_power_is_projplane_order`, is classical: for every prime power
`n = p ^ k` there is a finite projective plane of order `n`. We prove exactly that formal statement.
The witness is the Desarguesian plane `PG(2, q)` over the finite field `K = GaloisField p k`
(`q = p ^ k`): points and lines are both `ℙ K (Fin 3 → K)`, with incidence given by orthogonality,
as already packaged in Mathlib (`Configuration.ofField`). Counting points two ways gives
`order² + order + 1 = q² + q + 1`, and injectivity of `x ↦ x² + x + 1` on `ℕ` gives `order = q`.
-/

namespace Math0.Erdos723

open Configuration
open scoped LinearAlgebra.Projectivization

/-- The map `x ↦ x² + x + 1` is injective on `ℕ`. -/
lemma sq_add_add_one_injective {a b : ℕ} (h : a ^ 2 + a + 1 = b ^ 2 + b + 1) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
    omega
  · exact hab
  · have : b ^ 2 < a ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
    omega

/-- For every prime power `n` there is a finite projective plane of order `n`, namely the
projective plane over the finite field with `n` elements. -/
theorem prime_power_is_projplane_order :
    type_of% @Erdos723.erdos_723.variants.prime_power_is_projplane_order := by
  intro n hn
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
  have : Fact p.Prime := ⟨hp⟩
  classical
  let K := GaloisField p k
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (ℙ K (Fin 3 → K)) := Fintype.ofFinite _
  refine ⟨ℙ K (Fin 3 → K), ℙ K (Fin 3 → K), inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  -- number of points via the order of the plane
  have h1 := ProjectivePlane.card_points (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K))
  -- number of points of `ℙ² (K)` via `|K|`
  have h2 : Nat.card (ℙ K (Fin 3 → K)) = ∑ i ∈ Finset.range 3, Nat.card K ^ i :=
    Projectivization.card_of_finrank K (Fin 3 → K) (by simp)
  have hK : Nat.card K = p ^ k := GaloisField.card p k hk.ne'
  rw [Nat.card_eq_fintype_card, h1, hK] at h2
  simp [Finset.sum_range_succ] at h2
  apply sq_add_add_one_injective
  linarith

end Math0.Erdos723

#math0_proves Math0.Erdos723.prime_power_is_projplane_order Erdos723.erdos_723.variants.prime_power_is_projplane_order
