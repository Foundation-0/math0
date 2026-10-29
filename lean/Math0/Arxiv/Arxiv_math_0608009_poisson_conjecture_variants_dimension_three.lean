/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Arxiv.«math.0608009».PoissonConjecture
import Math0.Audit

/-!
# The Poisson conjecture fails in dimension three

The Poisson conjecture $PC_n$ of Adjamagbo and van den Essen (arXiv:math/0608009) asserts that
every endomorphism of the canonical Poisson algebra $K[x_1,\dots,x_n,y_1,\dots,y_n]$ over a
field of characteristic zero is an automorphism. We prove exactly the formal statement
`Arxiv.«math.0608009».poisson_conjecture.variants.dimension_three`, i.e. `¬ PC_3`.
The witness is the cotangent (symplectic) lift of the Jacobian-determinant-one, non-injective
polynomial map `G : K³ → K³` recorded in `FormalConjectures.Wikipedia.JacobianConjecture`:
$x_i \mapsto G_i(x)$ and $y_k \mapsto \sum_l A_{kl}(x)\, y_l$, where $A = \operatorname{adj}(JG)$
is the (polynomial) inverse of the Jacobian matrix. The bracket relations reduce to
$A \cdot JG = 1$ and to an explicit polynomial identity for the entries of $A$ (checked by `ring`).
The lift is not surjective: it identifies the points $(1,0,1,0,0,0)$ and $(0,3,-71,0,0,0)$, which
`x_1` separates, so `x_1` is not in its image.
-/

namespace Math0.Arxiv.«math.0608009»

-- Helpers live in `Dim3` to avoid clashes with sibling files for the same paper.
namespace Dim3

open MvPolynomial JacobianConjecture _root_.Arxiv.«math.0608009»

variable {K : Type*} [Field K]

/-- The first coordinate of `K³`. -/
noncomputable abbrev x₀ : MvPolynomial (Fin 3) K := X 0
/-- The second coordinate of `K³`. -/
noncomputable abbrev x₁ : MvPolynomial (Fin 3) K := X 1
/-- The third coordinate of `K³`. -/
noncomputable abbrev x₂ : MvPolynomial (Fin 3) K := X 2

/-- Entry `(0, 0)` of the adjugate of the Jacobian matrix of `G`, in expanded form. -/
noncomputable def a00 : MvPolynomial (Fin 3) K :=
  24 * x₀ ^ 6 * x₁ * x₂ + 72 * x₀ ^ 5 * x₁ ^ 2 + 12 * x₀ ^ 5 * x₂ + 12 * x₀ ^ 4 * x₁ - 8 * x₀ ^ 3

/-- Entry `(0, 1)` of the adjugate of the Jacobian matrix of `G`, in expanded form. -/
noncomputable def a01 : MvPolynomial (Fin 3) K :=
  12 * x₀ ^ 4 * x₁ * x₂ + 36 * x₀ ^ 3 * x₁ ^ 2 + 6 * x₀ ^ 3 * x₂ + 6 * x₀ ^ 2 * x₁ - 3 * x₀

/-- Entry `(0, 2)` of the adjugate of the Jacobian matrix of `G`, in expanded form. -/
noncomputable def a02 : MvPolynomial (Fin 3) K :=
  -72 * x₀ ^ 5 * x₁ * x₂ ^ 2 - 360 * x₀ ^ 4 * x₁ ^ 2 * x₂ - 36 * x₀ ^ 4 * x₂ ^ 2 - 432 * x₀ ^ 3 * x₁ ^ 3 - 120 * x₀ ^ 3 * x₁ * x₂ - 108 * x₀ ^ 2 * x₁ ^ 2 + 18 * x₀ ^ 2 * x₂ + 42 * x₀ * x₁ + 1

/-- Entry `(1, 0)` of the adjugate of the Jacobian matrix of `G`, in expanded form. -/
noncomputable def a10 : MvPolynomial (Fin 3) K :=
  -24 * x₀ ^ 6 * x₁ ^ 2 * x₂ - 72 * x₀ ^ 5 * x₁ ^ 3 - 24 * x₀ ^ 5 * x₁ * x₂ - 48 * x₀ ^ 4 * x₁ ^ 2 - 6 * x₀ ^ 4 * x₂ + 2 * x₀ ^ 3 * x₁ + 3 * x₀ ^ 2

/-- Entry `(1, 1)` of the adjugate of the Jacobian matrix of `G`, in expanded form. -/
noncomputable def a11 : MvPolynomial (Fin 3) K :=
  -12 * x₀ ^ 4 * x₁ ^ 2 * x₂ - 36 * x₀ ^ 3 * x₁ ^ 3 - 12 * x₀ ^ 3 * x₁ * x₂ - 24 * x₀ ^ 2 * x₁ ^ 2 - 3 * x₀ ^ 2 * x₂ + 1

/-- Entry `(1, 2)` of the adjugate of the Jacobian matrix of `G`, in expanded form. -/
noncomputable def a12 : MvPolynomial (Fin 3) K :=
  72 * x₀ ^ 5 * x₁ ^ 2 * x₂ ^ 2 + 360 * x₀ ^ 4 * x₁ ^ 3 * x₂ + 72 * x₀ ^ 4 * x₁ * x₂ ^ 2 + 432 * x₀ ^ 3 * x₁ ^ 4 + 300 * x₀ ^ 3 * x₁ ^ 2 * x₂ + 18 * x₀ ^ 3 * x₂ ^ 2 + 324 * x₀ ^ 2 * x₁ ^ 3 + 42 * x₀ ^ 2 * x₁ * x₂ + 12 * x₀ * x₁ ^ 2 - 6 * x₀ * x₂ - 16 * x₁

/-- Entry `(2, 0)` of the adjugate of the Jacobian matrix of `G`, in expanded form. -/
noncomputable def a20 : MvPolynomial (Fin 3) K :=
  96 * x₀ ^ 6 * x₁ ^ 4 * x₂ + 288 * x₀ ^ 5 * x₁ ^ 5 + 192 * x₀ ^ 5 * x₁ ^ 3 * x₂ + 480 * x₀ ^ 4 * x₁ ^ 4 + 144 * x₀ ^ 4 * x₁ ^ 2 * x₂ + 256 * x₀ ^ 3 * x₁ ^ 3 + 48 * x₀ ^ 3 * x₁ * x₂ + 36 * x₀ ^ 2 * x₁ ^ 2 + 6 * x₀ ^ 2 * x₂ - 6 * x₀ * x₁ - 1

/-- Entry `(2, 1)` of the adjugate of the Jacobian matrix of `G`, in expanded form. -/
noncomputable def a21 : MvPolynomial (Fin 3) K :=
  48 * x₀ ^ 4 * x₁ ^ 4 * x₂ + 144 * x₀ ^ 3 * x₁ ^ 5 + 96 * x₀ ^ 3 * x₁ ^ 3 * x₂ + 240 * x₀ ^ 2 * x₁ ^ 4 + 72 * x₀ ^ 2 * x₁ ^ 2 * x₂ + 132 * x₀ * x₁ ^ 3 + 24 * x₀ * x₁ * x₂ + 24 * x₁ ^ 2 + 3 * x₂

/-- Entry `(2, 2)` of the adjugate of the Jacobian matrix of `G`, in expanded form. -/
noncomputable def a22 : MvPolynomial (Fin 3) K :=
  -288 * x₀ ^ 5 * x₁ ^ 4 * x₂ ^ 2 - 1440 * x₀ ^ 4 * x₁ ^ 5 * x₂ - 576 * x₀ ^ 4 * x₁ ^ 3 * x₂ ^ 2 - 1728 * x₀ ^ 3 * x₁ ^ 6 - 2640 * x₀ ^ 3 * x₁ ^ 4 * x₂ - 432 * x₀ ^ 3 * x₁ ^ 2 * x₂ ^ 2 - 3024 * x₀ ^ 2 * x₁ ^ 5 - 1728 * x₀ ^ 2 * x₁ ^ 3 * x₂ - 144 * x₀ ^ 2 * x₁ * x₂ ^ 2 - 1776 * x₀ * x₁ ^ 4 - 468 * x₀ * x₁ ^ 2 * x₂ - 18 * x₀ * x₂ ^ 2 - 356 * x₁ ^ 3 - 42 * x₁ * x₂

/-- The adjugate of the Jacobian matrix of `G`, written out explicitly. -/
noncomputable def adjG : Fin 3 → Fin 3 → MvPolynomial (Fin 3) K :=
  ![![a00, a01, a02], ![a10, a11, a12], ![a20, a21, a22]]

set_option maxHeartbeats 4000000 in
/-- `adjG` is the adjugate of the (upstream) Jacobian matrix of `G`. -/
theorem adjugate_eq (i j : Fin 3) : (G K).Jacobian.adjugate i j = adjG i j := by
  fin_cases i <;> fin_cases j <;>
  simp only [G, RegularFunction.Jacobian, Matrix.adjugate_fin_three, Matrix.of_apply,
    adjG, a00, a01, a02, a10, a11, a12, a20, a21, a22,
    x₀, x₁, x₂, ← map_ofNat (C : K →+* MvPolynomial (Fin 3) K),
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_add, map_neg, Derivation.map_one_eq_zero,
    pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
  simp only [map_ofNat] <;> ring

/-- Since `det (JG) = 1`, the adjugate is a left inverse of the Jacobian matrix. -/
theorem adjG_mul (k i : Fin 3) :
    ∑ m, adjG k m * pderiv m (G K i) = if k = i then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.adjugate_mul (G K).Jacobian) k) i
  rw [det_jacobian_G, one_smul, Matrix.mul_apply, Matrix.one_apply] at h
  simp only [adjugate_eq] at h
  simp only [RegularFunction.Jacobian, Matrix.of_apply] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- The integrability identity that makes the momenta of the lift Poisson-commute. -/
theorem adjG_comm (k l a : Fin 3) :
    ∑ m, (pderiv m (adjG k a : MvPolynomial (Fin 3) K) * adjG l m -
      adjG k m * pderiv m (adjG l a)) = 0 := by
  fin_cases k <;> fin_cases l <;> fin_cases a <;>
  simp only [Fin.sum_univ_three, adjG, a00, a01, a02, a10, a11, a12, a20, a21, a22,
    x₀, x₁, x₂, ← map_ofNat (C : K →+* MvPolynomial (Fin 3) K),
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_add, map_neg, map_sub, Derivation.map_one_eq_zero,
    pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
  simp only [map_ofNat] <;> ring

/-- Polynomials in the position variables do not depend on the momentum variables. -/
theorem pderiv_inr_rename (m : Fin 3) (f : MvPolynomial (Fin 3) K) :
    pderiv (Sum.inr m) (rename (Sum.inl : Fin 3 → Fin 3 ⊕ Fin 3) f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n h => simp [h]

/-- The `k`-th momentum of the cotangent lift: `∑ l, A k l (x) * y l`. -/
noncomputable def mom (k : Fin 3) : MvPolynomial (Fin 3 ⊕ Fin 3) K :=
  ∑ l, rename Sum.inl (adjG k l) * X (Sum.inr l)

/-- Derivative of a momentum with respect to a momentum variable. -/
theorem pderiv_inr_mom (m k : Fin 3) :
    pderiv (Sum.inr m) (mom k : MvPolynomial (Fin 3 ⊕ Fin 3) K) =
      rename Sum.inl (adjG k m) := by
  simp [mom, pderiv_inr_rename, pderiv_X, Pi.single_apply]

/-- Derivative of a momentum with respect to a position variable. -/
theorem pderiv_inl_mom (m k : Fin 3) :
    pderiv (Sum.inl m) (mom k : MvPolynomial (Fin 3 ⊕ Fin 3) K) =
      ∑ l, rename Sum.inl (pderiv m (adjG k l)) * X (Sum.inr l) := by
  simp [mom, pderiv_rename Sum.inl_injective, mul_comm]

/-- The images of two position variables Poisson-commute. -/
theorem bracket_pos_pos (i j : Fin 3) :
    poissonBracket (rename Sum.inl (G K i) : MvPolynomial (Fin 3 ⊕ Fin 3) K)
      (rename Sum.inl (G K j)) = 0 := by
  simp [poissonBracket, pderiv_inr_rename]

/-- The image of a position variable and the image of a momentum variable are canonically
paired. -/
theorem bracket_pos_mom (i k : Fin 3) :
    poissonBracket (rename Sum.inl (G K i) : MvPolynomial (Fin 3 ⊕ Fin 3) K) (mom k) =
      if i = k then 1 else 0 := by
  simp only [poissonBracket, pderiv_inr_mom, pderiv_inr_rename, zero_mul, sub_zero,
    pderiv_rename Sum.inl_injective, ← map_mul, ← map_sum]
  have h := adjG_mul (K := K) k i
  simp_rw [mul_comm (pderiv _ (G K i))]
  rw [h]
  rcases eq_or_ne k i with rfl | hne
  · simp
  · simp [hne, hne.symm]

/-- The images of two momentum variables Poisson-commute. -/
theorem bracket_mom_mom (k l : Fin 3) :
    poissonBracket (mom k : MvPolynomial (Fin 3 ⊕ Fin 3) K) (mom l) = 0 := by
  simp only [poissonBracket, pderiv_inl_mom, pderiv_inr_mom]
  have h := fun a => congrArg (rename (Sum.inl : Fin 3 → Fin 3 ⊕ Fin 3)) (adjG_comm (K := K) k l a)
  simp only [map_sum, map_sub, map_mul, map_zero] at h
  simp only [Fin.sum_univ_three] at h ⊢
  linear_combination X (Sum.inr 0) * h 0 + X (Sum.inr 1) * h 1 + X (Sum.inr 2) * h 2

variable (K) in
/-- The cotangent lift of `G`: `x i ↦ G i (x)`, `y k ↦ ∑ l, A k l (x) * y l`. -/
noncomputable def lift :
    MvPolynomial (Fin 3 ⊕ Fin 3) K →ₐ[K] MvPolynomial (Fin 3 ⊕ Fin 3) K :=
  aeval (Sum.elim (fun i => rename Sum.inl (G K i)) mom)

/-- The cotangent lift of `G` preserves the canonical Poisson bracket. -/
theorem isPoissonEndomorphism_lift : IsPoissonEndomorphism (lift K) := by
  intro v w
  rcases v with i | k <;> rcases w with j | l
  · simp [lift, bracket_pos_pos]
  · simp [lift, bracket_pos_mom]
  · rw [poissonBracket_swap, poissonBracket_X_inr_inl]
    simp only [lift, aeval_X, Sum.elim_inl, Sum.elim_inr, bracket_pos_mom]
    rcases eq_or_ne k j with rfl | hne
    · simp
    · simp [hne, hne.symm]
  · simp [lift, bracket_mom_mom]

/-- The cotangent lift of `G` is not surjective: `x 0` is not in its image. -/
theorem not_surjective_lift : ¬ Function.Surjective (lift K) := by
  intro hs
  obtain ⟨f, hf⟩ := hs (X (Sum.inl 0))
  have key : ∀ r : Fin 3 ⊕ Fin 3 → K,
      aeval r (lift K f) = aeval (fun v => aeval r (lift K (X v))) f := fun r => by
    rw [lift, comp_aeval_apply]
    simp
  have hpq : (fun v => aeval (Sum.elim ![1, 0, 1] 0 : Fin 3 ⊕ Fin 3 → K) (lift K (X v))) =
      (fun v => aeval (Sum.elim ![0, 3, -71] 0 : Fin 3 ⊕ Fin 3 → K) (lift K (X v))) := by
    funext v
    rcases v with i | k
    · simp only [lift, aeval_X, Sum.elim_inl, aeval_rename, Sum.elim_comp_inl]
      exact congrFun (aeval_G_eq K) i
    · simp [lift, mom]
  have h1 := key (Sum.elim ![1, 0, 1] 0)
  have h2 := key (Sum.elim ![0, 3, -71] 0)
  rw [hf, hpq, ← h2, hf] at h1
  simp at h1

end Dim3

/-- The Poisson conjecture fails in dimension three: over every field of characteristic zero,
the cotangent lift of the Jacobian-determinant-one map `G` is a non-surjective (hence
non-bijective) endomorphism of the canonical Poisson algebra `P₃(K)`. -/
theorem poisson_conjecture_dimension_three :
    type_of% @Arxiv.«math.0608009».poisson_conjecture.variants.dimension_three := by
  intro K _ _ h
  exact Dim3.not_surjective_lift (h (Dim3.lift K) Dim3.isPoissonEndomorphism_lift).2

end Math0.Arxiv.«math.0608009»

#math0_proves Math0.Arxiv.«math.0608009».poisson_conjecture_dimension_three Arxiv.«math.0608009».poisson_conjecture.variants.dimension_three
