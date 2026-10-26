/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A144637
import Math0.Audit

/-!
# A144637: `(1/18) 6^n a(n) / n!` is odd iff `n = 2^k`, `k ≥ 1`

We prove Peter Bala's conjecture for column `2` of A144633.

**Composition.** Let `f(x) = x + x^2/2 + x^3/6`. Row `d` of A144385 has e.g.f. `f^d / d!`
(`fS_pow`, by comparing derivatives with the A144385 recurrence). The defining relation of the
inverse matrix, `∑_j T(j,2) S(j,n) = [n = 2]`, says exactly that the e.g.f.
`A(x) = ∑ a(n) x^n / n!` satisfies `A(f(x)) = x^2/2` (`subst_Aser`, using Mathlib's
`PowerSeries.subst`). Since `(x^2/2)` and `f` satisfy `2u^3 + 3u^2 + 18(1+f)u = 9f^2` with
`u = x^2/2`, and substitution of `f` is injective (triangular with unit diagonal), we get
`2A^3 + 3A^2 + 18(1+x)A = 9x^2` (`Aser_cubic`).

**Integer recursion.** With `Y(x) = A(6x)/18 = ∑ y(n) x^n` this becomes
`Y = x^2 - 6xY - 3Y^2 - 36Y^3` (`Yser_cubic`). As `y(0) = 0`, the coefficient of `x^n` on the
right only involves `y(i)` with `i < n`, so every `y(n)` is an integer (`y_mem`) and `Y` lifts to
`Z ∈ ℤ[[x]]` with the same equation.

**Parity.** Reducing mod `2` gives `W = x^2 + W^2` in `𝔽₂[[x]]`, and in characteristic `2`,
`[x^n] W^2 = [2 ∣ n] w(n/2)`. Hence `w(n) = [n = 2] + [2 ∣ n] w(n/2)` with `w(0) = 0`, and
strong induction gives `w(n) = 1 ↔ n = 2^k` with `k ≥ 1` (`parity`).
-/

namespace Math0.Frontier.A144637
open Math0.Statements.A144637
open PowerSeries Nat

/-- `f(x) = x + x^2/2 + x^3/6`, the e.g.f. of a single block of size `1`, `2` or `3`. -/
private noncomputable def fS : ℚ⟦X⟧ := X + C (1 / 2 : ℚ) * X ^ 2 + C (1 / 6 : ℚ) * X ^ 3

/-- The coefficients of `f`. -/
private lemma coeff_fS (n : ℕ) : coeff n fS =
    if n = 1 then 1 else if n = 2 then 1 / 2 else if n = 3 then 1 / 6 else 0 := by
  simp only [fS, map_add, coeff_C_mul, coeff_X_pow, coeff_X]
  rcases n with _ | _ | _ | _ | n <;> simp

/-- `f(0) = 0`. -/
private lemma constantCoeff_fS : constantCoeff fS = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_fS]; simp

/-- `f' = 1 + x + x^2/2`. -/
private lemma derivative_fS : d⁄dX ℚ fS = 1 + X + C (1 / 2 : ℚ) * X ^ 2 := by
  ext n
  rw [coeff_derivative, coeff_fS]
  simp only [map_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]
  rcases n with _ | _ | _ | n
  · norm_num
  · norm_num
  · norm_num
  · split_ifs <;> first | (exfalso; omega) | norm_num

/-- The exact halving `(m+2)(m+1)/2` in `ℕ`, cast to `ℚ`. -/
private lemma cast_half (m : ℕ) :
    (((m + 2) * (m + 1) / 2 : ℕ) : ℚ) = (m + 2) * (m + 1) / 2 := by
  have h : 2 ∣ (m + 2) * (m + 1) := by
    rw [mul_comm]; exact even_iff_two_dvd.mp (Nat.even_mul_succ_self (m + 1))
  rw [Nat.cast_div h (by norm_num)]
  push_cast; ring

/-- `S(d+1, 0) = 0`. -/
private lemma S_zero_right (d : ℕ) : S (d + 1) 0 = 0 := S_eq_zero_of_lt (by omega)

/-- Row `d` of A144385 has e.g.f. `f^d / d!`: `f^d = d! · ∑ S(d,k) x^k / k!`. Proved by
comparing derivatives, using the A144385 recurrence `S_succ`. -/
private lemma fS_pow (d : ℕ) :
    fS ^ d = C (d ! : ℚ) * mk (fun k => (S d k : ℚ) / (k ! : ℚ)) := by
  induction d with
  | zero =>
    ext k
    rw [pow_zero, coeff_one, coeff_C_mul, coeff_mk, S_zero]
    rcases k with _ | k <;> simp
  | succ d ih =>
    apply derivative.ext
    · rw [derivative_pow, Nat.add_sub_cancel, ih, derivative_fS]
      set G := mk (fun k => (S d k : ℚ) / (k ! : ℚ)) with hG
      have e :
          ((d + 1 : ℕ) : ℚ⟦X⟧) * (C (d ! : ℚ) * G) * (1 + X + C (1 / 2 : ℚ) * X ^ 2) =
          C (((d + 1 : ℕ) : ℚ) * d !) * (G + X * G + C (1 / 2 : ℚ) * (X ^ 2 * G)) := by
        simp only [map_mul, map_natCast]; ring
      rw [e]
      ext k
      rw [coeff_derivative, coeff_C_mul, coeff_C_mul, coeff_mk, S_succ, map_add, map_add,
        coeff_C_mul, coeff_X_pow_mul']
      rcases k with _ | _ | k
      · simp only [coeff_zero_X_mul, hG, coeff_mk]
        simp [Nat.factorial]
      · simp only [coeff_succ_X_mul, hG, coeff_mk]
        simp [Nat.factorial]
        ring
      · simp only [coeff_succ_X_mul, hG, coeff_mk]
        rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
          show k + 1 + 1 + 1 - 1 = k + 2 by omega, show k + 1 + 1 + 1 - 2 = k + 1 by omega,
          show k + 1 + 1 + 1 - 3 = k by omega, show k + 1 + 1 - 2 = k by omega]
        push_cast
        rw [cast_half]
        simp only [Nat.factorial_succ]
        push_cast
        field_simp
        ring
    · rw [map_pow, constantCoeff_fS, map_mul, constantCoeff_C,
        ← coeff_zero_eq_constantCoeff_apply (mk _), coeff_mk, S_zero_right]
      simp

/-- `f` can be substituted into power series (its constant term is `0`). -/
private lemma hasSubst_fS : HasSubst fS := HasSubst.of_constantCoeff_zero' constantCoeff_fS

/-- `[x^k] f^d = d! S(d,k) / k!`. -/
private lemma coeff_fS_pow (d k : ℕ) :
    coeff k (fS ^ d) = (d ! : ℚ) * (S d k : ℚ) / (k ! : ℚ) := by
  rw [fS_pow, coeff_C_mul, coeff_mk]; ring

/-- The coefficients of the composition `Q(f(x))`, as a finite sum. -/
private lemma coeff_subst_fS (Q : ℚ⟦X⟧) (n : ℕ) :
    coeff n (Q.subst fS) =
      ∑ d ∈ Finset.range (n + 1), coeff d Q * ((d ! : ℚ) * S d n / n !) := by
  rw [coeff_subst' hasSubst_fS, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · simp only [coeff_fS_pow, smul_eq_mul]
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hd
    rw [coeff_fS_pow, S_eq_zero_of_lt (by omega)]
    simp

/-- Composition with `f` is injective: the system is triangular with unit diagonal
(`S(n,n) = 1`). -/
private lemma subst_fS_inj (Q : ℚ⟦X⟧) (h : Q.subst fS = 0) : Q = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have e := coeff_subst_fS Q n
    rw [h, map_zero, Finset.sum_range_succ, Finset.sum_eq_zero
      (fun d hd => by rw [ih d (Finset.mem_range.mp hd), map_zero, zero_mul]), S_self,
      Nat.cast_one, mul_one, div_self (by positivity), mul_one, zero_add] at e
    rw [map_zero, ← e]

/-- `A(x) = ∑ a(n) x^n / n!`, the e.g.f. of column `2` of A144633. -/
private noncomputable def Aser : ℚ⟦X⟧ := mk (fun n => (a n : ℚ) / (n ! : ℚ))

/-- `A(f(x)) = x^2/2`: this is exactly the defining relation `∑_j T(j,2) S(j,n) = [n = 2]`
of the inverse matrix (`sum_T_mul_S`). -/
private lemma subst_Aser : Aser.subst fS = C (1 / 2 : ℚ) * X ^ 2 := by
  ext n
  rw [coeff_subst_fS, coeff_C_mul, coeff_X_pow]
  have key := sum_T_mul_S 2 n (n + 1) (Nat.lt_succ_self n)
  have e : ∑ d ∈ Finset.range (n + 1), coeff d Aser * ((d ! : ℚ) * S d n / n !) =
      ((∑ d ∈ Finset.range (n + 1), T d 2 * (S d n : ℤ) : ℤ) : ℚ) / n ! := by
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    simp only [Aser, coeff_mk, a]
    push_cast
    field_simp
  rw [e, key]
  by_cases hn : n = 2
  · subst hn; norm_num [Nat.factorial]
  · rw [if_neg (Ne.symm hn), if_neg hn]; simp

/-- The algebraic equation `2A^3 + 3A^2 + 18(1+x)A = 9x^2`: substituting `f` turns it into a
polynomial identity (since `A(f) = x^2/2`), and substitution by `f` is injective. -/
private lemma Aser_cubic :
    2 * Aser ^ 3 + 3 * Aser ^ 2 + 18 * (1 + X) * Aser - 9 * X ^ 2 = 0 := by
  apply subst_fS_inj
  rw [← coe_substAlgHom hasSubst_fS]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one, substAlgHom_X]
  rw [coe_substAlgHom, subst_Aser, fS]
  have hu : 2 * C (1 / 2 : ℚ) = 1 := by
    rw [← map_ofNat C 2, ← map_mul]; norm_num
  have hv : 6 * C (1 / 6 : ℚ) = 1 := by
    rw [← map_ofNat C 6, ← map_mul]; norm_num
  set u := C (1 / 2 : ℚ)
  set v := C (1 / 6 : ℚ)
  linear_combination (6*X^6*u^2*v + 18*X^6*u*v^2 + 54*X^6*v^3 + 36*X^4*u*v + 108*X^4*v^2 +
    54*X^2*v) * hu + (-2*X^6*u^3 - 6*X^6*u^2*v - 18*X^6*u*v^2 + 9*X^6*v^2 - 12*X^4*u^2 -
    36*X^4*u*v + 18*X^4*v - 18*X^2*u + 9*X^2) * hv

/-- `Y(x) = ∑ y(n) x^n = A(6x)/18`. -/
private noncomputable def Yser : ℚ⟦X⟧ := mk (fun n => y n)

/-- `Y(x) = A(6x)/18`. -/
private lemma Yser_eq : Yser = C (1 / 18 : ℚ) * rescale (6 : ℚ) Aser := by
  ext n
  simp only [Yser, Aser, y, coeff_mk, coeff_C_mul, coeff_rescale]
  ring

/-- `Y = x^2 - 6xY - 3Y^2 - 36Y^3`. -/
private lemma Yser_cubic : Yser = X ^ 2 - C (6 : ℚ) * (X * Yser) - C (3 : ℚ) * (Yser * Yser) -
    C (36 : ℚ) * (Yser * (Yser * Yser)) := by
  have h := congrArg (rescale (6 : ℚ)) Aser_cubic
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one, rescale_X, map_zero] at h
  have h18 : 18 * C (1 / 18 : ℚ) = 1 := by
    rw [← map_ofNat C 18, ← map_mul]; norm_num
  have h6 : C (6 : ℚ) = 6 := map_ofNat C 6
  have h3 : C (3 : ℚ) = 3 := map_ofNat C 3
  have h36 : C (36 : ℚ) = 36 := map_ofNat C 36
  rw [h6, h3, h36, Yser_eq]
  set c := C (1 / 18 : ℚ)
  set B := rescale (6 : ℚ) Aser
  have h324 : (324 : ℚ⟦X⟧) * (c * B - (X ^ 2 - 6 * (X * (c * B)) - 3 * (c * B * (c * B)) -
      36 * (c * B * (c * B * (c * B))))) = 0 := by
    linear_combination h + B * (648 * B ^ 2 * c ^ 2 + 36 * B ^ 2 * c + 2 * B ^ 2 + 54 * B * c +
      3 * B + 108 * X + 18) * h18
  have hne : (324 : ℚ⟦X⟧) ≠ 0 := by
    intro h0
    have := congrArg (coeff 0) h0
    rw [← map_ofNat C 324, coeff_C, if_pos rfl, map_zero] at this
    norm_num at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h324).resolve_left hne)

/-- `y(0) = 0`. -/
private lemma y_zero : y 0 = 0 := by
  simp [y, a, T_eq_zero_of_lt (show 0 < 2 by norm_num)]

/-- The subring of rationals that are integers. -/
private abbrev Zr : Subring ℚ := (Int.castRingHom ℚ).range

/-- The coefficients of `Y` are the `y(n)`. -/
private lemma coeff_Yser (n : ℕ) : coeff n Yser = y n := coeff_mk _ _

/-- `[x^j] Y^2` is an integer when `y(i)` is for all `i < j` (as `y(0) = 0`). -/
private lemma sq_mem (j : ℕ) (hj : ∀ i < j, y i ∈ Zr) : coeff j (Yser * Yser) ∈ Zr := by
  rw [coeff_mul]
  refine Subring.sum_mem _ fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [coeff_Yser, coeff_Yser]
  by_cases h1 : p.1 = 0
  · rw [h1, y_zero, zero_mul]; exact Subring.zero_mem _
  by_cases h2 : p.2 = 0
  · rw [h2, y_zero, mul_zero]; exact Subring.zero_mem _
  exact Subring.mul_mem _ (hj _ (by omega)) (hj _ (by omega))

/-- `[x^j] Y^3` is an integer when `y(i)` is for all `i < j` (as `y(0) = 0`). -/
private lemma cube_mem (j : ℕ) (hj : ∀ i < j, y i ∈ Zr) :
    coeff j (Yser * (Yser * Yser)) ∈ Zr := by
  rw [coeff_mul]
  refine Subring.sum_mem _ fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [coeff_Yser]
  by_cases h1 : p.1 = 0
  · rw [h1, y_zero, zero_mul]; exact Subring.zero_mem _
  by_cases h2 : p.2 = 0
  · rw [h2, coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply,
      coeff_Yser, y_zero, zero_mul, mul_zero]
    exact Subring.zero_mem _
  exact Subring.mul_mem _ (hj _ (by omega)) (sq_mem _ fun i hi => hj i (by omega))

/-- Every `y(n)` is an integer (strong induction on the recursion from `Yser_cubic`). -/
private lemma y_mem (n : ℕ) : y n ∈ Zr := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [← coeff_Yser, Yser_cubic]
    simp only [map_sub, coeff_C_mul]
    refine Subring.sub_mem _ (Subring.sub_mem _ (Subring.sub_mem _ ?_ ?_) ?_) ?_
    · rw [coeff_X_pow]; split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · refine Subring.mul_mem _ ⟨6, by simp⟩ ?_
      rcases n with _ | n
      · rw [coeff_zero_X_mul]; exact Subring.zero_mem _
      · rw [coeff_succ_X_mul, coeff_Yser]; exact ih n (by omega)
    · exact Subring.mul_mem _ ⟨3, by simp⟩ (sq_mem n ih)
    · exact Subring.mul_mem _ ⟨36, by simp⟩ (cube_mem n ih)

/-- `Y` is the image of an integer power series `Z` satisfying the same cubic equation. -/
private lemma exists_Z : ∃ Z : ℤ⟦X⟧, map (Int.castRingHom ℚ) Z = Yser ∧
    Z = X ^ 2 - 6 * X * Z - 3 * Z ^ 2 - 36 * Z ^ 3 := by
  choose z hz using fun n => y_mem n
  refine ⟨mk z, ?_, ?_⟩
  · ext n; rw [coeff_map, coeff_mk, hz, coeff_Yser]
  · have hm : map (Int.castRingHom ℚ) (mk z) = Yser := by
      ext n; rw [coeff_map, coeff_mk, hz, coeff_Yser]
    apply map_injective (Int.castRingHom ℚ) Int.cast_injective
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_X, hm]
    have h6 : C (6 : ℚ) = 6 := map_ofNat C 6
    have h3 : C (3 : ℚ) = 3 := map_ofNat C 3
    have h36 : C (36 : ℚ) = 36 := map_ofNat C 36
    have := Yser_cubic
    rw [h6, h3, h36] at this
    linear_combination this

/-- In characteristic `2`, `[x^n] W^2 = [2 ∣ n] · [x^(n/2)] W` (Frobenius, via
`ZMod.expand_card` on a truncation). -/
private lemma coeff_mul_self_two (W : (ZMod 2)⟦X⟧) (n : ℕ) :
    coeff n (W * W) = if 2 ∣ n then coeff (n / 2) W else 0 := by
  rw [coeff_mul_eq_coeff_trunc_mul_trunc W W (Nat.lt_succ_self n), ← Polynomial.coe_mul,
    Polynomial.coeff_coe, ← sq, ← ZMod.expand_card, Polynomial.coeff_expand two_pos,
    coeff_trunc]
  split_ifs with h1 h2
  · rfl
  · exfalso; apply h2; omega
  · rfl

/-- If `W ∈ 𝔽₂[[x]]` has `W(0) = 0` and `W = x^2 + W^2`, then `[x^n] W = 1` exactly when
`n = 2^k` with `k ≥ 1`. -/
private lemma parity (W : (ZMod 2)⟦X⟧) (h0 : coeff 0 W = 0) (hW : W = X ^ 2 + W * W)
    (n : ℕ) :
    coeff n W = 1 ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k := by
  have hrec : ∀ m, coeff m W = (if m = 2 then 1 else 0) +
      (if 2 ∣ m then coeff (m / 2) W else 0) := by
    intro m
    conv_lhs => rw [hW]
    rw [map_add, coeff_X_pow, coeff_mul_self_two]
  have h1 : coeff 1 W = 0 := by rw [hrec]; simp
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | n
    · rw [h0]
      constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨k, -, hk⟩; exact absurd hk.symm (pow_ne_zero _ (by norm_num))
    · rw [h1]
      constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨k, hk1, hk⟩
        have : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
        omega
    · rw [hrec, if_pos rfl, if_pos (by norm_num), show (0 + 1 + 1) / 2 = 1 by norm_num, h1]
      simp only [add_zero, true_iff]
      exact ⟨1, le_rfl, rfl⟩
    · rw [hrec, if_neg (by omega), zero_add]
      by_cases hd : 2 ∣ n + 1 + 1 + 1
      · have ih' : coeff ((n + 1 + 1 + 1) / 2) W = 1 ↔
            ∃ k : ℕ, 1 ≤ k ∧ (n + 1 + 1 + 1) / 2 = 2 ^ k := ih _ (by omega)
        rw [if_pos hd, ih']
        obtain ⟨m, hm⟩ := hd
        rw [hm, Nat.mul_div_cancel_left _ (by norm_num)]
        constructor
        · rintro ⟨k, hk1, hk⟩
          exact ⟨k + 1, by omega, by rw [hk, pow_succ]; ring⟩
        · rintro ⟨k, hk1, hk⟩
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          refine ⟨j, ?_, ?_⟩
          · rcases j with _ | j
            · simp at hk; omega
            · omega
          · rw [pow_succ] at hk; omega
      · rw [if_neg hd]
        constructor
        · intro h; exact absurd h (by decide)
        · rintro ⟨k, hk1, hk⟩
          exfalso
          apply hd
          rw [hk]
          exact dvd_pow_self 2 (by omega)

/-- Bala's conjecture holds: `y(n)` is an odd integer iff `n = 2^k` with `k ≥ 1`. -/
theorem result : statement := by
  obtain ⟨Z, hZ, hZc⟩ := exists_Z
  set W := map (Int.castRingHom (ZMod 2)) Z with hWdef
  have hW : W = X ^ 2 + W * W := by
    have h := congrArg (map (Int.castRingHom (ZMod 2))) hZc
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_X] at h
    have h2 : (2 : (ZMod 2)⟦X⟧) = 0 := by
      rw [← map_ofNat C 2]
      rw [show (OfNat.ofNat 2 : ZMod 2) = 0 by decide, map_zero]
    linear_combination h - (3 * X * W + 2 * W ^ 2 + 18 * W ^ 3) * h2
  have hz : ∀ n, ((coeff n Z : ℤ) : ℚ) = y n := by
    intro n
    rw [← coeff_Yser, ← hZ, coeff_map]; rfl
  have hw : ∀ n, coeff n W = ((coeff n Z : ℤ) : ZMod 2) := by
    intro n; rw [hWdef, coeff_map]; rfl
  have h0 : coeff 0 W = 0 := by
    rw [hw]
    have : ((coeff 0 Z : ℤ) : ℚ) = ((0 : ℤ) : ℚ) := by rw [hz, y_zero]; simp
    rw [Int.cast_injective this]; simp
  intro n
  rw [← parity W h0 hW n, hw, ZMod.intCast_eq_one_iff_odd]
  constructor
  · rintro ⟨m, hm, hy⟩
    have : coeff n Z = m := Int.cast_injective ((hz n).trans hy)
    rw [this]; exact hm
  · intro h
    exact ⟨coeff n Z, h, (hz n).symm⟩

end Math0.Frontier.A144637

#math0_settles Math0.Frontier.A144637.result Math0.Statements.A144637.statement
