/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Arxiv.«math.0608009».PoissonConjecture
import Math0.Audit

/-!
# The Jacobian conjecture in dimension `2n` implies the Poisson conjecture in dimension `n`

Adjamagbo and van den Essen [AvdE07, Theorems 1 and 7] observed that $JC_{2n}$ implies $PC_n$:
every endomorphism of the canonical Poisson algebra $P_n(K)$ is an automorphism, provided the
Jacobian conjecture holds in $2n$ variables. We prove exactly the formal statement
`Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication` from
formal-conjectures. If `φ` preserves the canonical bracket on generators, its Jacobian matrix
`B` (with `B a w = ∂_a φ(X_w)`) satisfies `Bᵀ J B = J` for Mathlib's symplectic form `J`,
so `B` is symplectic and `det B` is a unit. After reindexing the variables by
`Fin (2n) ≃ Fin n ⊕ Fin n`, the Jacobian conjecture provides a polynomial two-sided inverse
`G` of `F = (φ(X_v))_v`; then `bind₁ G` inverts `bind₁ F`, and `φ` is a conjugate of `bind₁ F`
by renaming isomorphisms, hence bijective. The characteristic-zero hypothesis is not used.
-/

open MvPolynomial JacobianConjecture Matrix

namespace Math0.Arxiv.«math.0608009»

section Helpers

variable {K : Type*} [Field K]

/-- The Poisson bracket of the components of a polynomial map is, up to sign, the
congruence of Mathlib's symplectic form `J` by its Jacobian matrix:
`(Bᵀ J B) v w = -{f v, f w}` where `B a w = ∂_a (f w)`. -/
theorem jacobian_transpose_J_jacobian {n : ℕ}
    (f : Fin n ⊕ Fin n → MvPolynomial (Fin n ⊕ Fin n) K) :
    (RegularFunction.Jacobian f)ᵀ * Matrix.J (Fin n) (MvPolynomial (Fin n ⊕ Fin n) K) *
      RegularFunction.Jacobian f = Matrix.of fun v w => -poissonBracket (f v) (f w) := by
  refine Matrix.ext fun v w => ?_
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, RegularFunction.Jacobian,
    poissonBracket, Matrix.one_apply, Finset.sum_sub_distrib]
  ring

/-- The Jacobian matrix of the identity map `X` is the identity matrix. -/
theorem jacobian_X {σ : Type*} [Fintype σ] [DecidableEq σ] :
    RegularFunction.Jacobian (X : σ → MvPolynomial σ K) = 1 := by
  refine Matrix.ext fun a b => ?_
  simp [RegularFunction.Jacobian, Matrix.one_apply, Pi.single_apply, eq_comm]

/-- The Jacobian matrix of a Poisson endomorphism is symplectic, so its determinant is a
unit. -/
theorem isUnit_det_jacobian {n : ℕ}
    (φ : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin n ⊕ Fin n) K)
    (hφ : Arxiv.«math.0608009».IsPoissonEndomorphism φ) :
    IsUnit (RegularFunction.Jacobian fun v => φ (X v)).det := by
  have hmem : (RegularFunction.Jacobian fun v => φ (X v)) ∈
      symplecticGroup (Fin n) (MvPolynomial (Fin n ⊕ Fin n) K) := by
    rw [SymplecticGroup.mem_iff', jacobian_transpose_J_jacobian]
    have h1 := jacobian_transpose_J_jacobian (K := K) (n := n) X
    rw [jacobian_X, transpose_one, Matrix.one_mul, Matrix.mul_one] at h1
    rw [h1]
    refine Matrix.ext fun v w => ?_
    simp only [Matrix.of_apply]
    rw [hφ v w]
  exact SymplecticGroup.symplectic_det hmem

/-- Transporting a polynomial map along a bijection `e` of the variables transports its
Jacobian matrix by reindexing and renaming. -/
theorem jacobian_rename {σ τ : Type*} [Fintype σ] [Fintype τ] (e : σ ≃ τ)
    (f : τ → MvPolynomial τ K) :
    RegularFunction.Jacobian (fun i => rename e.symm (f (e i))) =
      ((RegularFunction.Jacobian f).submatrix e e).map (rename e.symm) := by
  refine Matrix.ext fun a b => ?_
  simp only [RegularFunction.Jacobian, Matrix.of_apply, Matrix.map_apply, Matrix.submatrix_apply]
  have := pderiv_rename (R := K) e.symm.injective (e a) (f (e b))
  simpa using this

/-- Assuming the Jacobian conjecture in `2n` variables, an algebra endomorphism of
`K[X_v : v ∈ Fin n ⊕ Fin n]` whose Jacobian determinant is a unit is bijective. -/
theorem bijective_of_jacobianConjecture {n : ℕ} (h : JacobianConjectureProp K (Fin (2 * n)))
    (φ : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin n ⊕ Fin n) K)
    (hφ : IsUnit (RegularFunction.Jacobian fun v => φ (X v)).det) :
    Function.Bijective φ := by
  set e : Fin (2 * n) ≃ Fin n ⊕ Fin n := (finCongr (two_mul n)).trans finSumFinEquiv.symm
  set F : RegularFunction K (Fin (2 * n)) (Fin (2 * n)) := fun i => rename e.symm (φ (X (e i)))
  have hF : IsUnit F.Jacobian.det := by
    have hJ : F.Jacobian = _ := jacobian_rename e (fun v => φ (X v))
    have hd := RingHom.map_det
      ((rename e.symm : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin (2 * n)) K) :
        MvPolynomial (Fin n ⊕ Fin n) K →+* MvPolynomial (Fin (2 * n)) K)
      ((RegularFunction.Jacobian fun v => φ (X v)).submatrix e e)
    rw [RingHom.mapMatrix_apply, det_submatrix_equiv_self] at hd
    rw [hJ]
    convert hφ.map
      (rename e.symm : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin (2 * n)) K)
    exact hd.symm
  obtain ⟨G, hGF, hFG⟩ := h F hF
  have h1 : (bind₁ G).comp (bind₁ F) = AlgHom.id K _ := by
    rw [bind₁_comp_bind₁]
    have : (fun i => bind₁ G (F i)) = X := hGF
    rw [this, bind₁_X_left]
  have h2 : (bind₁ F).comp (bind₁ G) = AlgHom.id K _ := by
    rw [bind₁_comp_bind₁]
    have : (fun i => bind₁ F (G i)) = X := hFG
    rw [this, bind₁_X_left]
  have hbF : Function.Bijective (bind₁ F) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨bind₁ G, fun p => ?_, fun p => ?_⟩
    · exact congrArg
        (fun ψ : MvPolynomial (Fin (2 * n)) K →ₐ[K] MvPolynomial (Fin (2 * n)) K => ψ p) h1
    · exact congrArg
        (fun ψ : MvPolynomial (Fin (2 * n)) K →ₐ[K] MvPolynomial (Fin (2 * n)) K => ψ p) h2
  have hφeq : φ = (rename e).comp ((bind₁ F).comp (rename e.symm)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [F, rename_rename]
  rw [hφeq]
  exact (renameEquiv K e).bijective.comp (hbF.comp (renameEquiv K e.symm).bijective)

end Helpers

/-- The Jacobian conjecture in dimension `2n` implies the Poisson conjecture in dimension `n`
([AvdE07], Theorems 1 and 7): if every polynomial self-map of `K^(2n)` with unit Jacobian
determinant has a polynomial inverse, then every endomorphism of the canonical Poisson algebra
`P_n(K)` is bijective. -/
theorem jacobian_implication :
    type_of% @Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication := by
  intro K _ _ n h φ hφ
  exact bijective_of_jacobianConjecture h φ (isUnit_det_jacobian φ hφ)

end Math0.Arxiv.«math.0608009»

#math0_proves Math0.Arxiv.«math.0608009».jacobian_implication Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication
