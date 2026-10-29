/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A267486
import Math0.Audit

/-!
# O'Sullivan's Gaussian-polynomial / Chebyshev representation (A267486)

We prove the general conjecture stated in A267486: for all `m, n ≥ 0`, with
`N = n + ⌊m/2⌋` (so that `2n + m + 1 - (m mod 2) = 2N + 1`), the row polynomial
`G(m;n,x) = [t^m] (1+t) ∏_{k=1}^N (1 + t² + 2t T_k(x/2))` has degree at most `g(m;n)` and
`[2N+1, m]_q = ∑_{k ≤ g} [x^k]G(m;n,x) · (1+q²)^k q^(g-k)`.

**Idea.** Substitute `x = q + q⁻¹` (the ring hom `φ : ℚ[x] → ℚ[q, q⁻¹]`). Then
`2 T_k(x/2) ↦ q^k + q^(-k)` (from the Chebyshev recursion), so each factor becomes
`(1 + q^k t)(1 + q^(-k) t)` and the whole product is `∏_{j=0}^{2N} (1 + q^(j-N) t)`
(`symProd`). The q-binomial theorem (`qbinom`, by induction from the q-Pascal rule that
defines `gaussBinom`) gives `[t^m] = q^(-Nm) q^(m(m-1)/2) [2N+1, m]_q`, i.e.
`φ(G) = q^(-g) [2N+1, m]_q` since `g = Nm - m(m-1)/2`. On the other side, for `deg P ≤ g`,
`∑_k [x^k]P (1+q²)^k q^(g-k) = q^g φ(P)` (`hom_eq`), and `Polynomial.toLaurent` is injective.

The degree bound `deg G ≤ g` is proved separately by induction on `N` (`deg_F`):
`2 deg_x [t^m] F_N + m² ≤ m (2N+1)` for `m ≤ 2N+1`, where `F_N` is the product with `N`
Chebyshev factors and `deg 2T_k(x/2) ≤ k`.
-/

namespace Math0.Frontier.A267486
open Math0.Statements.A267486
open Polynomial
open scoped LaurentPolynomial

/-- `2 T_0(x/2) = 2`. -/
private theorem chebHalf_zero : 2 * chebHalf 0 = 2 := by
  simp [chebHalf]

/-- The Chebyshev recursion for `2 T_k(x/2)`: `a_{k+2} = x a_{k+1} - a_k`. -/
private theorem chebHalf_add_two (k : ℕ) :
    2 * chebHalf (k + 2) = X * (2 * chebHalf (k + 1)) - 2 * chebHalf k := by
  have h := Chebyshev.T_add_two ℚ (k : ℤ)
  simp only [chebHalf]
  push_cast
  rw [h]
  simp only [sub_comp, mul_comp, ofNat_comp, X_comp, Nat.cast_ofNat]
  have hp : (2 : ℚ[X]) * (C (1 / 2 : ℚ) * X) = X := by
    rw [← mul_assoc, ← C_ofNat, ← C_mul]; norm_num
  linear_combination (2 * (Chebyshev.T ℚ ((k : ℤ) + 1)).comp (C (1 / 2 : ℚ) * X)) * hp

/-- `deg 2 T_k(x/2) ≤ k` (stated for two consecutive indices, for the induction). -/
private theorem natDegree_chebHalf (k : ℕ) : (2 * chebHalf k).natDegree ≤ k ∧
    (2 * chebHalf (k + 1)).natDegree ≤ k + 1 := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [chebHalf_zero]; simp
    · rw [two_chebHalf_one]; simp
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [chebHalf_add_two]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_mul_le).trans ?_
      have := ih.2
      have h1 : (X : ℚ[X]).natDegree ≤ 1 := natDegree_X_le
      omega
    · have := ih.1; omega

/-- The substitution `x ↦ q + q⁻¹`, as a ring hom `ℚ[x] → ℚ[q, q⁻¹]`. -/
private noncomputable def φ : ℚ[X] →+* ℚ[T;T⁻¹] :=
  (aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : ℚ[T;T⁻¹])).toRingHom

/-- `q · q⁻¹ = 1` in `ℚ[q, q⁻¹]`. -/
private theorem T_mul_T :
    (LaurentPolynomial.T 1 : ℚ[T;T⁻¹]) * LaurentPolynomial.T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add]; simp

/-- `2 T_k((q + q⁻¹)/2) = q^k + q^(-k)`. -/
private theorem φ_chebHalf (k : ℕ) :
    φ (2 * chebHalf k) = LaurentPolynomial.T 1 ^ k + LaurentPolynomial.T (-1) ^ k ∧
    φ (2 * chebHalf (k + 1)) =
      LaurentPolynomial.T 1 ^ (k + 1) + LaurentPolynomial.T (-1) ^ (k + 1) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [chebHalf_zero, map_ofNat]; norm_num
    · rw [two_chebHalf_one]; simp [φ]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [chebHalf_add_two, map_sub, map_mul, ih.1, ih.2]
    have hX : φ X = LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) := by simp [φ]
    rw [hX]
    linear_combination (LaurentPolynomial.T 1 ^ k + LaurentPolynomial.T (-1) ^ k) * T_mul_T

/-- The q-binomial theorem: `[t^m] ∏_{j<M} (1 + u q^j t) = u^m q^(m choose 2) [M,m]_q`. -/
private theorem qbinom {R : Type*} [CommRing R] (q : R) :
    ∀ (M m : ℕ) (u : R), (∏ j ∈ Finset.range M, (1 + C (u * q ^ j) * X : R[X])).coeff m =
      u ^ m * q ^ (m.choose 2) * aeval q (gaussBinom M m) := by
  intro M
  induction M with
  | zero =>
    intro m u
    cases m with
    | zero => simp [gaussBinom]
    | succ m => simp [gaussBinom, coeff_one]
  | succ M ih =>
    intro m u
    rw [Finset.prod_range_succ']
    have hc : ∀ j ∈ Finset.range M, (1 + C (u * q ^ (j + 1)) * X : R[X]) =
        1 + C ((u * q) * q ^ j) * X := by
      intro j _
      rw [show u * q ^ (j + 1) = (u * q) * q ^ j by ring]
    rw [Finset.prod_congr rfl hc]
    rw [pow_zero, mul_one, mul_add, mul_one, coeff_add, ← mul_assoc]
    cases m with
    | zero =>
      rw [coeff_mul_X_zero, add_zero, ih]
      simp [gaussBinom]
    | succ m =>
      rw [coeff_mul_X, coeff_mul_C, ih, ih]
      simp only [gaussBinom, map_add, map_mul, map_pow, aeval_X]
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
      ring

/-- `(1+t) ∏_{k=1}^N (1 + t^2 + t (q^k + q^{-k})) = ∏_{j=0}^{2N} (1 + q^{j-N} t)`. -/
private theorem symProd {R : Type*} [CommRing R] (q qi : R) (h : q * qi = 1) (N : ℕ) :
    (1 + X) * ∏ k ∈ Finset.Icc 1 N, (1 + X ^ 2 + X * C (q ^ k + qi ^ k) : R[X]) =
      ∏ j ∈ Finset.range (2 * N + 1), (1 + C (qi ^ N * q ^ j) * X) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ← mul_assoc, ih,
      show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.prod_range_succ _ (2 * N + 1 + 1),
      Finset.prod_range_succ' _ (2 * N + 1)]
    have hc : ∀ j ∈ Finset.range (2 * N + 1), (1 + C (qi ^ (N + 1) * q ^ (j + 1)) * X : R[X]) =
        1 + C (qi ^ N * q ^ j) * X := by
      intro j _
      rw [show qi ^ (N + 1) * q ^ (j + 1) = qi ^ N * q ^ j by
        linear_combination (qi ^ N * q ^ j) * h]
    rw [Finset.prod_congr rfl hc, mul_assoc]
    congr 1
    have h1 : qi ^ (N + 1) * q ^ (2 * N + 1 + 1) = q ^ (N + 1) := by
      rw [show qi ^ (N + 1) * q ^ (2 * N + 1 + 1) = q ^ (N + 1) * (q * qi) ^ (N + 1) by ring,
        h, one_pow, mul_one]
    have h2 : (C (q ^ (N + 1)) * C (qi ^ (N + 1)) : R[X]) = 1 := by
      rw [← map_mul, ← mul_pow, h, one_pow, map_one]
    rw [h1, pow_zero, mul_one, map_add]
    linear_combination (-X ^ 2 : R[X]) * h2

/-- `G(m;n,t,x)` with `N = n + ⌊m/2⌋` factors. -/
private noncomputable def F (N : ℕ) : ℚ[X][X] :=
  (1 + X) * ∏ k ∈ Finset.Icc 1 N, (1 + X ^ 2 + 2 * X * C (chebHalf k))

/-- Adding the factor `k = N+1` to `F N`. -/
private theorem F_succ (N : ℕ) :
    F (N + 1) = F N * (1 + X ^ 2 + X * C (2 * chebHalf (N + 1))) := by
  rw [F, F, Finset.prod_Icc_succ_top (by omega), mul_assoc, C_mul, C_ofNat]
  ring

/-- `F N` has `t`-degree at most `2N+1`. -/
private theorem natDegree_F (N : ℕ) : (F N).natDegree ≤ 2 * N + 1 := by
  induction N with
  | zero => simp only [F, Finset.Icc_eq_empty_of_lt (show 0 < 1 by norm_num),
      Finset.prod_empty, mul_one]; compute_degree!
  | succ N ih =>
    rw [F_succ]
    refine natDegree_mul_le.trans ?_
    have : (1 + X ^ 2 + X * C (2 * chebHalf (N + 1)) : ℚ[X][X]).natDegree ≤ 2 := by
      compute_degree!
    omega

/-- The `t`-coefficients of `p · (1 + t² + t c)`. -/
private theorem coeff_factor (p : ℚ[X][X]) (c : ℚ[X]) (m : ℕ) :
    (p * (1 + X ^ 2 + X * C c)).coeff 0 = p.coeff 0 ∧
    (p * (1 + X ^ 2 + X * C c)).coeff 1 = p.coeff 1 + p.coeff 0 * c ∧
    (p * (1 + X ^ 2 + X * C c)).coeff (m + 2) =
      p.coeff (m + 2) + p.coeff m + p.coeff (m + 1) * c := by
  have e : p * (1 + X ^ 2 + X * C c) = p + p * X ^ 2 + p * C c * X := by ring
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · rw [coeff_add, coeff_add, coeff_mul_X, coeff_mul_C]
    simp [coeff_mul_X_pow']
  · rw [coeff_add, coeff_add, coeff_mul_X, coeff_mul_C, coeff_mul_X_pow]

/-- The `x`-degree bound `2 deg [t^m] F_N + m² ≤ m (2N+1)` for `m ≤ 2N+1`. -/
private theorem deg_F (N : ℕ) :
    ∀ m, m ≤ 2 * N + 1 → 2 * ((F N).coeff m).natDegree + m * m ≤ m * (2 * N + 1) := by
  induction N with
  | zero =>
    intro m hm
    have hF : F 0 = 1 + X := by simp [F]
    interval_cases m <;> simp [hF, coeff_one, coeff_X]
  | succ N ih =>
    intro m hm
    have hz : ∀ j, 2 * N + 1 < j → (F N).coeff j = 0 := fun j hj =>
      coeff_eq_zero_of_natDegree_lt ((natDegree_F N).trans_lt hj)
    have ha := (natDegree_chebHalf (N + 1)).1
    rw [F_succ]
    rcases m with _ | _ | m
    · rw [(coeff_factor _ _ 0).1]
      have := ih 0 (by omega)
      omega
    · rw [(coeff_factor _ _ 0).2.1]
      have h1 := ih 1 (by omega)
      have h0 := ih 0 (by omega)
      have hd := (natDegree_add_le ((F N).coeff 1) ((F N).coeff 0 * (2 * chebHalf (N + 1)))).trans
        (max_le_max le_rfl natDegree_mul_le)
      have e1 : 1 * (2 * N + 1) = 2 * N + 1 := by ring
      have e2 : 1 * (2 * (N + 1) + 1) = 2 * N + 3 := by ring
      omega
    · rw [(coeff_factor _ _ m).2.2]
      have hB := ih m (by omega)
      have hd := (natDegree_add_le _ _).trans (max_le_max (natDegree_add_le
        ((F N).coeff (m + 2)) ((F N).coeff m)) (natDegree_mul_le (p := (F N).coeff (m + 1))
          (q := 2 * chebHalf (N + 1))))
      have hA : 2 * ((F N).coeff (m + 2)).natDegree + (m + 2) * (m + 2) ≤ (m + 2) * (2 * N + 1)
          ∨ ((F N).coeff (m + 2)).natDegree = 0 := by
        by_cases h : m + 2 ≤ 2 * N + 1
        · exact Or.inl (ih _ h)
        · right; rw [hz _ (by omega)]; simp
      have hC : 2 * ((F N).coeff (m + 1)).natDegree + (m + 1) * (m + 1) ≤ (m + 1) * (2 * N + 1)
          ∨ m = 2 * N + 1 := by
        by_cases h : m + 1 ≤ 2 * N + 1
        · exact Or.inl (ih _ h)
        · right; omega
      have e1 : (m + 2) * (m + 2) = m * m + 4 * m + 4 := by ring
      have e2 : (m + 2) * (2 * (N + 1) + 1) = 2 * (m * N) + 3 * m + 4 * N + 6 := by ring
      have e3 : m * (2 * N + 1) = 2 * (m * N) + m := by ring
      have e4 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      have e5 : (m + 1) * (2 * N + 1) = 2 * (m * N) + m + 2 * N + 1 := by ring
      have e6 : (m + 2) * (2 * N + 1) = 2 * (m * N) + m + 4 * N + 2 := by ring
      have e7 : (m + 1 + 1) * (m + 1 + 1) = m * m + 4 * m + 4 := by ring
      have e8 : (m + 1 + 1) * (2 * (N + 1) + 1) = 2 * (m * N) + 3 * m + 4 * N + 6 := by ring
      have hd' : ((F N).coeff (m + 2) + (F N).coeff m + (F N).coeff (m + 1) *
          (2 * chebHalf (N + 1))).natDegree ≤ ((F N).coeff (m + 2)).natDegree ∨
          ((F N).coeff (m + 2) + (F N).coeff m + (F N).coeff (m + 1) *
          (2 * chebHalf (N + 1))).natDegree ≤ ((F N).coeff m).natDegree ∨
          ((F N).coeff (m + 2) + (F N).coeff m + (F N).coeff (m + 1) *
          (2 * chebHalf (N + 1))).natDegree ≤ ((F N).coeff (m + 1)).natDegree +
            (2 * chebHalf (N + 1)).natDegree := by
        rcases le_max_iff.mp hd with h | h
        · rcases le_max_iff.mp h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      rcases hC with hC | hC
      · rcases hA with hA | hA <;> rcases hd' with hd' | hd' | hd' <;> omega
      · subst hC
        rw [hz (2 * N + 1 + 1) (by omega), zero_mul, add_zero]
        have := (natDegree_add_le ((F N).coeff (2 * N + 1 + 2)) ((F N).coeff (2 * N + 1)))
        omega

/-- `toLaurent` of an integer polynomial is its evaluation at `q`. -/
private theorem toLaurent_map_int (p : ℤ[X]) :
    toLaurent (p.map (Int.castRingHom ℚ)) = aeval (LaurentPolynomial.T 1 : ℚ[T;T⁻¹]) p := by
  have : (toLaurent : ℚ[X] →+* ℚ[T;T⁻¹]).comp (mapRingHom (Int.castRingHom ℚ)) =
      (aeval (LaurentPolynomial.T 1 : ℚ[T;T⁻¹])).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp
  exact RingHom.congr_fun this p

/-- For `deg P ≤ d`: `∑_{k ≤ d} [x^k]P (1+q²)^k q^(d-k) = q^d P(q + q⁻¹)`. -/
private theorem hom_eq (P : ℚ[X]) (d : ℕ) (hP : P.natDegree ≤ d) :
    toLaurent (∑ k ∈ Finset.range (d + 1), C (P.coeff k) * (1 + X ^ 2) ^ k * X ^ (d - k)) =
      LaurentPolynomial.T 1 ^ d * φ P := by
  have hφ : φ P = ∑ k ∈ Finset.range (d + 1),
      P.coeff k • (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : ℚ[T;T⁻¹]) ^ k :=
    aeval_eq_sum_range' (by omega) _
  rw [hφ, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := by rw [Finset.mem_range] at hk; omega
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hk'
  rw [show d - k = e by omega, he]
  simp only [map_mul, map_pow, map_add, map_one, toLaurent_C, toLaurent_X, Algebra.smul_def]
  rw [← LaurentPolynomial.C_eq_algebraMap]
  have h1 : (1 + LaurentPolynomial.T 1 ^ 2 : ℚ[T;T⁻¹]) =
      LaurentPolynomial.T 1 * (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) := by
    linear_combination (-1 : ℚ[T;T⁻¹]) * T_mul_T
  rw [h1, mul_pow]
  ring

/-- `G(m;n, q + q⁻¹) = q^(-Nm) q^(m choose 2) [2N+1, m]_q`. -/
private theorem φ_G (m n : ℕ) :
    φ (G m n) = (LaurentPolynomial.T (-1) ^ (n + (m - m % 2) / 2)) ^ m *
      LaurentPolynomial.T 1 ^ (m.choose 2) *
        aeval (LaurentPolynomial.T 1 : ℚ[T;T⁻¹])
          (gaussBinom (2 * (n + (m - m % 2) / 2) + 1) m) := by
  have hGt : Gt m n = F (n + (m - m % 2) / 2) := rfl
  rw [G_eq_coeff, hGt, ← coeff_map]
  have hF : ∀ N, (F N).map φ = (1 + X) * ∏ k ∈ Finset.Icc 1 N,
      (1 + X ^ 2 + X * C ((LaurentPolynomial.T 1 ^ k + LaurentPolynomial.T (-1) ^ k :
        ℚ[T;T⁻¹]))) := by
    intro N
    have hfac : ∀ k, (1 + X ^ 2 + 2 * X * C (chebHalf k) : ℚ[X][X]) =
        1 + X ^ 2 + X * C (2 * chebHalf k) := fun k => by rw [C_mul, C_ofNat]; ring
    unfold F
    simp only [hfac]
    rw [Polynomial.map_mul, Polynomial.map_prod]
    simp only [Polynomial.map_add, Polynomial.map_one, Polynomial.map_X, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_C, (φ_chebHalf _).1]
  rw [hF, symProd _ _ T_mul_T, qbinom]
  rfl

/-- O'Sullivan's conjecture (A267486) holds. -/
theorem result : statement := by
  intro m n
  set N := n + (m - m % 2) / 2 with hN
  have hM : 2 * n + m + 1 - m % 2 = 2 * N + 1 := by omega
  have hmN : m ≤ 2 * N + 1 := by omega
  have hg : 2 * g m n + m * m = m * (2 * N + 1) := by
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · have h1 : N = n + j := by omega
      have h2 : g (2 * j) n = (2 * n + 1) * j := by
        simp only [g, show 2 * j % 2 = 0 by omega]
        simp only [zero_ne_one, if_false]
        rw [show (2 * n + 1) * (2 * j) = 2 * ((2 * n + 1) * j) by ring,
          Nat.mul_div_cancel_left _ (by norm_num)]
      rw [h1, h2]; ring
    · have h1 : N = n + j := by omega
      have h2 : g (2 * j + 1) n = (2 * j + 1) * n := by
        simp only [g, show (2 * j + 1) % 2 = 1 by omega, if_true]
      rw [h1, h2]; ring
  have hc : 2 * m.choose 2 + m = m * m := by
    clear hg hmN hM hN
    induction m with
    | zero => rfl
    | succ k ih => rw [Nat.choose_succ_succ', Nat.choose_one_right]; nlinarith
  have hgc : g m n + m.choose 2 = N * m := by
    have e : m * (2 * N + 1) = 2 * (N * m) + m := by ring
    omega
  have hdeg : (G m n).natDegree ≤ g m n := by
    have hGt : Gt m n = F N := rfl
    have := deg_F N m hmN
    rw [G_eq_coeff, hGt]
    omega
  refine ⟨hdeg, ?_⟩
  rw [hM]
  apply toLaurent_injective
  rw [toLaurent_map_int, hom_eq _ _ hdeg, φ_G, ← hN]
  have hTT : (LaurentPolynomial.T 1 : ℚ[T;T⁻¹]) ^ g m n *
      ((LaurentPolynomial.T (-1)) ^ N) ^ m * LaurentPolynomial.T 1 ^ m.choose 2 = 1 := by
    rw [← pow_mul, mul_right_comm, ← pow_add, hgc, mul_comm N m, ← mul_pow, mul_comm,
      mul_comm (LaurentPolynomial.T (-1)), T_mul_T, one_pow]
  rw [← mul_assoc, ← mul_assoc, hTT, one_mul]

end Math0.Frontier.A267486

#math0_settles Math0.Frontier.A267486.result Math0.Statements.A267486.statement
