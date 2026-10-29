/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A355360
import Math0.Audit

/-!
# Columns 1 and 2 of the theta-series triangle A355360 are `P(x)^3` and `2 P(x)^6`

We prove both conjectures of Paul D. Hanna in A355360: `T(n+1, 1) = A000716(n)` (partitions
into parts of 3 kinds) and `T(n+2, 2) = 2 · A023005(n)` (partitions into parts of 6 kinds).

**Mathematics.** Let `F(B) = ∑_{n ∈ ℤ} (-1)^n x^{T(n)} B^n` with `T(n) = n(n+1)/2`; grouping `n`
and `-1-n`, `F(B) = ∑_{n ≥ 0} (-1)^n x^{T(n)} (B^n - B^{-(n+1)})`. Work modulo `y^3`. Put
`u = x P^3`, `w = y u + 2 y^2 u^2` and `E = 1 + w`. Since `w^3 = 0`,
`E^n - E^{-(n+1)} = (1+w)^n - (1-w+w^2)^{n+1} = (2n+1)(w - w^2) = (2n+1)(y u + y^2 u^2)`, so
`F(E) = S · (y u + y^2 u^2)` with `S = ∑_{n ≥ 0} (-1)^n (2n+1) x^{T(n)}`. **Jacobi's identity**
`∏ (1 - x^k)^3 = S` gives `S P^3 = 1`, hence `S u = x` and `F(E) = x y (1 + y u) = x y E`
modulo `y^3`. The recursion of the entry (`coeffs`) is `a_{m+1} = y a_m - [x^{m+1}] F(A_{≤m})`,
and `[x^{m+1}] F(A_{≤m}) = [x^{m+1}] F(E) - e_{m+1}` when `A_{≤m}` is the truncation of `E` (only
the `n = 0` term `-B^{-1}` sees the missing coefficient). By induction `a_m ≡ e_m (mod y^3)`, so
column 1 is `u = x P^3` and column 2 is `2 u^2 = 2 x^2 P^6`.

**Jacobi's identity** is proved in the truncated form `(q;q)_n^3 ≡ ∑_{k ≤ n} (-1)^k (2k+1) q^{T(k)}
(mod q^{n+1})`. With Gaussian binomials `G(j,k) = (q;q)_{j+k} / ((q;q)_j (q;q)_k)` (in `ℤ⟦q⟧`), the
`q`-binomial theorem (two `q`-Pascal rules, induction) expands
`Φ(u) = ∏_{i<n} (q^{i+1} - u) ∏_{j ≤ n} (1 - u q^j) = ∑_i (-1)^i q^{e(i)} G(i, 2n+1-i) u^i`,
where `e(i) = (i-n)(i-n-1)/2`. As `Φ = (1 - u) Ψ` with `Ψ(1) = (-1)^n (q;q)_n^2`, differentiating
at `u = 1` gives `-(-1)^n (q;q)_n^2 = ∑_i i (-1)^i q^{e(i)} G(i, 2n+1-i)`. Multiplying by `(q;q)_n`,
each `q^{e(i)} G(i, 2n+1-i) (q;q)_n ≡ q^{e(i)} (mod q^{n+1})`, and pairing `i = n-k` with
`i = n+1+k` gives the claim. The partition generating function enters through the statement's
count `pb` (partitions with parts `≤ m`): `(∑ pb(n,m) q^n) (q;q)_m = 1`.

**Computation.** The lists of the statement are interpreted as polynomials in `y` (`ev`) and power
series in `x` (`evS`); `padd`, `pmul`, `smul`, `sinv`, `thetaCoeff` and `coeffs` are shown to
compute sums, products, truncated products, truncated inverses, the coefficient `[x^m] F(B)` and
the recursion above, over any commutative ring. We evaluate in `ℤ[y]/(y^3)`.
-/

namespace Math0.Frontier.A355360
open Math0.Statements.A355360
open PowerSeries Finset

variable {R : Type*} [CommRing R]


/-- Congruence of power series modulo `X ^ N`. -/
private def Cg (N : ℕ) (f g : R⟦X⟧) : Prop := (X : R⟦X⟧) ^ N ∣ f - g

/-- Reflexivity of the congruence modulo `X ^ N`. -/
private theorem Cg.rfl' {N : ℕ} {f : R⟦X⟧} : Cg N f f := by simp [Cg]

/-- Symmetry of the congruence modulo `X ^ N`. -/
private theorem Cg.symm {N : ℕ} {f g : R⟦X⟧} (h : Cg N f g) : Cg N g f := by
  unfold Cg at *; rw [← neg_sub]; exact (dvd_neg).2 h

/-- Transitivity of the congruence modulo `X ^ N`. -/
private theorem Cg.trans {N : ℕ} {f g h : R⟦X⟧} (h1 : Cg N f g) (h2 : Cg N g h) : Cg N f h := by
  unfold Cg at *; have := dvd_add h1 h2; rwa [sub_add_sub_cancel] at this

/-- Congruences modulo `X ^ N` can be added. -/
private theorem Cg.add {N : ℕ} {f g f' g' : R⟦X⟧} (h1 : Cg N f g) (h2 : Cg N f' g') :
    Cg N (f + f') (g + g') := by
  unfold Cg at *; rw [add_sub_add_comm]; exact dvd_add h1 h2

/-- Congruences modulo `X ^ N` can be subtracted. -/
private theorem Cg.sub {N : ℕ} {f g f' g' : R⟦X⟧} (h1 : Cg N f g) (h2 : Cg N f' g') :
    Cg N (f - f') (g - g') := by
  unfold Cg at *; have := dvd_sub h1 h2; rwa [sub_sub_sub_comm] at this

/-- Congruences modulo `X ^ N` can be multiplied. -/
private theorem Cg.mul {N : ℕ} {f g f' g' : R⟦X⟧} (h1 : Cg N f g) (h2 : Cg N f' g') :
    Cg N (f * f') (g * g') := by
  unfold Cg at *
  have : f * f' - g * g' = f * (f' - g') + (f - g) * g' := by ring
  rw [this]; exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_left h1 _)

/-- Congruences modulo `X ^ N` can be raised to powers. -/
private theorem Cg.pow {N : ℕ} {f g : R⟦X⟧} (h : Cg N f g) (k : ℕ) : Cg N (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact Cg.rfl'
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

/-- Congruences modulo `X ^ N` can be summed over a finset. -/
private theorem Cg.sum {ι : Type*} {N : ℕ} (s : Finset ι) {f g : ι → R⟦X⟧}
    (h : ∀ i ∈ s, Cg N (f i) (g i)) :
    Cg N (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  unfold Cg at *; rw [← Finset.sum_sub_distrib]; exact Finset.dvd_sum h

/-- A congruence modulo `X ^ N'` implies one modulo `X ^ N` for `N ≤ N'`. -/
private theorem Cg.mono {N N' : ℕ} {f g : R⟦X⟧} (hN : N ≤ N') (h : Cg N' f g) : Cg N f g :=
  (pow_dvd_pow _ hN).trans h

/-- Congruent power series modulo `X ^ N` have the same coefficients below `N`. -/
private theorem Cg.coeff_eq {N : ℕ} {f g : R⟦X⟧} (h : Cg N f g) {i : ℕ} (hi : i < N) :
    coeff i f = coeff i g := by
  have := (X_pow_dvd_iff.1 h) i hi
  rwa [map_sub, sub_eq_zero] at this

/-- Power series with the same coefficients below `N` are congruent modulo `X ^ N`. -/
private theorem cg_of_coeff {N : ℕ} {f g : R⟦X⟧} (h : ∀ i < N, coeff i f = coeff i g) : Cg N f g :=
  X_pow_dvd_iff.2 fun i hi => by rw [map_sub, h i hi, sub_self]

/-- Multiplying a congruence modulo `X ^ N` by `X ^ e` gives one modulo `X ^ (N + e)`. -/
private theorem Cg.X_pow_mul {N : ℕ} (e : ℕ) {f g : R⟦X⟧} (h : Cg N f g) :
    Cg (N + e) (X ^ e * f) (X ^ e * g) := by
  unfold Cg at *; rw [← mul_sub, pow_add, mul_comm ((X : R⟦X⟧) ^ N)]; exact mul_dvd_mul_left _ h

/-- Triangular numbers. -/
private def tri (k : ℕ) : ℕ := k * (k + 1) / 2

/-- `T(k+1) = T(k) + (k+1)`. -/
private theorem tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := by
  unfold tri
  rw [show (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) by ring,
    Nat.add_mul_div_left _ _ (by norm_num)]

/-- `k ≤ T(k)`. -/
private theorem le_tri (k : ℕ) : k ≤ tri k := by
  induction k with
  | zero => simp
  | succ k ih => rw [tri_succ]; omega

/-- `T(0) = 0`. -/
private theorem tri_zero : tri 0 = 0 := rfl

/-- `(q;q)_a`. -/
private noncomputable def qp (a : ℕ) : R⟦X⟧ := ∏ j ∈ range a, (1 - X ^ (j + 1))

/-- `(q;q)_{a+1} = (q;q)_a (1 - q^{a+1})`. -/
private theorem qp_succ (a : ℕ) : (qp (a + 1) : R⟦X⟧) = qp a * (1 - X ^ (a + 1)) :=
  prod_range_succ _ _

/-- `(q;q)_0 = 1`. -/
private theorem qp_zero : (qp 0 : R⟦X⟧) = 1 := prod_range_zero _

/-- `(q;q)_a` has constant coefficient `1`. -/
private theorem constantCoeff_qp (a : ℕ) : constantCoeff (qp a : R⟦X⟧) = 1 := by
  simp [qp, map_prod]

/-- The inverse `1/(q;q)_a` in `R⟦q⟧`. -/
private noncomputable def qpi (a : ℕ) : R⟦X⟧ := invOfUnit (qp a) 1

/-- `qpi a` is the inverse of `(q;q)_a`. -/
private theorem qp_mul_qpi (a : ℕ) : (qp a : R⟦X⟧) * qpi a = 1 :=
  mul_invOfUnit _ _ (by simp [constantCoeff_qp])

/-- `1/(q;q)_0 = 1`. -/
private theorem qpi_zero : (qpi 0 : R⟦X⟧) = 1 := by
  have := qp_mul_qpi (R := R) 0; rwa [qp_zero, one_mul] at this

/-- `1/(q;q)_a = (1 - q^{a+1}) / (q;q)_{a+1}`. -/
private theorem qpi_succ (a : ℕ) : (qpi a : R⟦X⟧) = (1 - X ^ (a + 1)) * qpi (a + 1) := by
  have h1 := qp_mul_qpi (R := R) a
  have h2 := qp_mul_qpi (R := R) (a + 1)
  rw [qp_succ] at h2
  linear_combination ((1 - X ^ (a + 1)) * qpi (a + 1)) * h1 - qpi a * h2

/-- Gaussian binomial `[j+k choose j]_q`. -/
private noncomputable def gb (j k : ℕ) : R⟦X⟧ := qp (j + k) * qpi j * qpi k

/-- Symmetry of the Gaussian binomial. -/
private theorem gb_comm (j k : ℕ) : (gb j k : R⟦X⟧) = gb k j := by
  unfold gb; rw [add_comm]; ring

/-- `[k choose 0]_q = 1`. -/
private theorem gb_zero_left (k : ℕ) : (gb 0 k : R⟦X⟧) = 1 := by
  unfold gb; rw [zero_add, qpi_zero, mul_one, qp_mul_qpi]

/-- `[j choose j]_q = 1`. -/
private theorem gb_zero_right (j : ℕ) : (gb j 0 : R⟦X⟧) = 1 := by
  rw [gb_comm, gb_zero_left]

/-- The `q`-Pascal rule `G(j+1,k+1) = G(j,k+1) + q^{j+1} G(j+1,k)`. -/
private theorem gb_pascalA (j k : ℕ) :
    (gb (j + 1) (k + 1) : R⟦X⟧) = gb j (k + 1) + X ^ (j + 1) * gb (j + 1) k := by
  unfold gb
  rw [qpi_succ j, qpi_succ k, show j + 1 + (k + 1) = (j + k + 1) + 1 by ring,
    show j + (k + 1) = j + k + 1 by ring, show j + 1 + k = j + k + 1 by ring, qp_succ (j + k + 1)]
  ring

/-- The `q`-Pascal rule `G(j+1,k+1) = q^{k+1} G(j,k+1) + G(j+1,k)`. -/
private theorem gb_pascalB (j k : ℕ) :
    (gb (j + 1) (k + 1) : R⟦X⟧) = X ^ (k + 1) * gb j (k + 1) + gb (j + 1) k := by
  rw [gb_comm, gb_pascalA, gb_comm k, gb_comm (k + 1)]; ring


/-- Exponent of `q` in the coefficient of `u^i` in `∏_{i<a} (q^{i+1} - u) ∏_{j<b} (1 - u q^j)`:
`(i-a)(i-a-1)/2`. -/
private def ex (a i : ℕ) : ℕ := if a < i then tri (i - a - 1) else tri (a - i)

/-- The exponent `ex` only depends on `i - a`. -/
private theorem ex_succ_succ (a i : ℕ) : ex (a + 1) (i + 1) = ex a i := by
  unfold ex
  by_cases h : a < i
  · rw [if_pos (by omega), if_pos h]; congr 1; omega
  · rw [if_neg (by omega), if_neg h]; congr 1; omega

/-- The exponent identity used by both `q`-Pascal steps: `a + 1 + ex a (i+1) = ex a i + i + 1`. -/
private theorem ex_step (a i : ℕ) : a + 1 + ex a (i + 1) = ex a i + (i + 1) := by
  unfold ex
  by_cases h : a < i
  · rw [if_pos (by omega), if_pos h, show i + 1 - a - 1 = (i - a - 1) + 1 by omega, tri_succ]
    omega
  · by_cases h' : a = i
    · subst h'; rw [if_pos (by omega), if_neg h]; simp [tri_zero]
    · rw [if_neg (by omega), if_neg h, show a - i = (a - (i + 1)) + 1 by omega, tri_succ]
      omega

/-- `ex a 0 = T(a)`. -/
private theorem ex_zero_right (a : ℕ) : ex a 0 = tri a := by
  unfold ex; rw [if_neg (by omega)]; rfl

/-- `ex a a = 0`. -/
private theorem ex_self (a : ℕ) : ex a a = 0 := by
  unfold ex; rw [if_neg (by omega), Nat.sub_self]; rfl

/-- The polynomial `∏_{i<a} (q^{i+1} - u) ∏_{j<b} (1 - u q^j)` in `u` over `R⟦q⟧`. -/
private noncomputable def Φ (a b : ℕ) : Polynomial R⟦X⟧ :=
  (∏ i ∈ range a, (Polynomial.C ((X : R⟦X⟧) ^ (i + 1)) - Polynomial.X)) *
  ∏ j ∈ range b, (1 - Polynomial.C ((X : R⟦X⟧) ^ j) * Polynomial.X)

/-- Claimed coefficients of `Φ a b`. -/
private noncomputable def cf (a b i : ℕ) : R⟦X⟧ :=
  if i ≤ a + b then (-1) ^ i * X ^ (ex a i) * gb i (a + b - i) else 0

/-- Coefficient `i+1` of a polynomial times the linear factor `α - β u`. -/
private theorem coeff_mul_lin {S : Type*} [CommRing S] (p : Polynomial S) (α β : S) (i : ℕ) :
    (p * (Polynomial.C α - Polynomial.C β * Polynomial.X)).coeff (i + 1) =
      p.coeff (i + 1) * α - p.coeff i * β := by
  rw [mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_C, ← mul_assoc,
    Polynomial.coeff_mul_X, Polynomial.coeff_mul_C]

/-- Constant coefficient of a polynomial times the linear factor `α - β u`. -/
private theorem coeff_mul_lin_zero {S : Type*} [CommRing S] (p : Polynomial S) (α β : S) :
    (p * (Polynomial.C α - Polynomial.C β * Polynomial.X)).coeff 0 = p.coeff 0 * α := by
  rw [mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_C, ← mul_assoc,
    Polynomial.coeff_mul_X_zero, sub_zero]

/-- Adding the factor `q^{a+1} - u` (with no factors of the second kind). -/
private theorem Φ_succ_left (a : ℕ) :
    (Φ (a + 1) 0 : Polynomial R⟦X⟧) =
      Φ a 0 * (Polynomial.C ((X : R⟦X⟧) ^ (a + 1)) - Polynomial.C 1 * Polynomial.X) := by
  simp only [Φ, prod_range_succ, prod_range_zero, mul_one, map_one, one_mul]

/-- Adding the factor `1 - u q^b`. -/
private theorem Φ_succ_right (a b : ℕ) :
    (Φ a (b + 1) : Polynomial R⟦X⟧) =
      Φ a b * (Polynomial.C 1 - Polynomial.C ((X : R⟦X⟧) ^ b) * Polynomial.X) := by
  simp only [Φ, prod_range_succ, map_one, mul_assoc]

/-- The constant coefficient changes correctly when the factor `q^{a+1} - u` is added. -/
private theorem cf_succ_left_zero (a : ℕ) : (cf (a + 1) 0 0 : R⟦X⟧) = cf a 0 0 * X ^ (a + 1) := by
  simp only [cf, Nat.zero_le, if_true, pow_zero, one_mul, gb_zero_left, mul_one, ex_zero_right,
    tri_succ, pow_add]

/-- The coefficient `i+1` changes correctly when the factor `q^{a+1} - u` is added. -/
private theorem cf_succ_left (a i : ℕ) :
    (cf (a + 1) 0 (i + 1) : R⟦X⟧) = cf a 0 (i + 1) * X ^ (a + 1) - cf a 0 i * 1 := by
  unfold cf
  rcases lt_trichotomy (i + 1) (a + 1) with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, a = i + 1 + k := ⟨a - (i + 1), by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      show i + 1 + k + 1 + 0 - (i + 1) = k + 1 by omega,
      show i + 1 + k + 0 - (i + 1) = k by omega, show i + 1 + k + 0 - i = k + 1 by omega,
      gb_pascalA, ex_succ_succ]
    have he := ex_step (i + 1 + k) i
    have hx : (X : R⟦X⟧) ^ ex (i + 1 + k) (i + 1) * X ^ (i + 1 + k + 1) =
        X ^ ex (i + 1 + k) i * X ^ (i + 1) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [pow_succ (-1 : R⟦X⟧) i]
    linear_combination ((-1 : R⟦X⟧) ^ i * gb (i + 1) k) * hx
  · have hi : i = a := by omega
    subst hi
    rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    simp only [Nat.add_zero, Nat.sub_self, ex_self, gb_zero_right]
    ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring

/-- The constant coefficient changes correctly when the factor `1 - u q^b` is added. -/
private theorem cf_succ_right_zero (a b : ℕ) : (cf a (b + 1) 0 : R⟦X⟧) = cf a b 0 * 1 := by
  simp only [cf, Nat.zero_le, if_true, pow_zero, one_mul, gb_zero_left, mul_one]

/-- The coefficient `i+1` changes correctly when the factor `1 - u q^b` is added. -/
private theorem cf_succ_right (a b i : ℕ) :
    (cf a (b + 1) (i + 1) : R⟦X⟧) = cf a b (i + 1) * 1 - cf a b i * X ^ b := by
  unfold cf
  rcases lt_trichotomy (i + 1) (a + b + 1) with h | h | h
  · obtain ⟨k, hk⟩ : ∃ k, a + b = i + 1 + k := ⟨a + b - (i + 1), by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      show a + (b + 1) - (i + 1) = k + 1 by omega,
      show a + b - (i + 1) = k by omega, show a + b - i = k + 1 by omega, gb_pascalB]
    have he := ex_step a i
    have hx : (X : R⟦X⟧) ^ ex a (i + 1) * X ^ (k + 1) = X ^ ex a i * X ^ b := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [pow_succ (-1 : R⟦X⟧) i]
    linear_combination (-(-1 : R⟦X⟧) ^ i * gb i (k + 1)) * hx
  · have hi : i = a + b := by omega
    subst hi
    rw [if_pos (by omega), if_neg (by omega), if_pos (by omega),
      show a + (b + 1) - (a + b + 1) = 0 by omega, Nat.sub_self, gb_zero_right, gb_zero_right]
    have he := ex_step a (a + b)
    have hx : (X : R⟦X⟧) ^ ex a (a + b + 1) = X ^ ex a (a + b) * X ^ b := by
      rw [← pow_add]; congr 1; omega
    rw [hx, pow_succ]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring

/-- The coefficient formula for the empty product. -/
private theorem coeff_Φ_zero_zero (i : ℕ) : (Φ 0 0 : Polynomial R⟦X⟧).coeff i = cf 0 0 i := by
  simp only [Φ, prod_range_zero, mul_one, Polynomial.coeff_one, cf]
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [ex_self, gb_zero_left]
  · rw [if_neg (by omega), if_neg (by omega)]

/-- The coefficient formula for `Φ a 0`. -/
private theorem coeff_Φ_left (a : ℕ) : ∀ i, (Φ a 0 : Polynomial R⟦X⟧).coeff i = cf a 0 i := by
  induction a with
  | zero => exact coeff_Φ_zero_zero
  | succ a ih =>
    intro i
    rw [Φ_succ_left]
    cases i with
    | zero => rw [coeff_mul_lin_zero, ih, cf_succ_left_zero]
    | succ i => rw [coeff_mul_lin, ih, ih, cf_succ_left]

/-- The `q`-binomial expansion: the coefficients of `Φ a b` are `cf a b i`. -/
private theorem coeff_Φ (a b : ℕ) : ∀ i, (Φ a b : Polynomial R⟦X⟧).coeff i = cf a b i := by
  induction b with
  | zero => exact coeff_Φ_left a
  | succ b ih =>
    intro i
    rw [Φ_succ_right]
    cases i with
    | zero => rw [coeff_mul_lin_zero, ih, cf_succ_right_zero]
    | succ i => rw [coeff_mul_lin, ih, ih, cf_succ_right]


/-- `Ψ n`, with `Φ n (n+1) = (1 - u) Ψ n`. -/
private noncomputable def Ψ (n : ℕ) : Polynomial R⟦X⟧ :=
  (∏ i ∈ range n, (Polynomial.C ((X : R⟦X⟧) ^ (i + 1)) - Polynomial.X)) *
  ∏ j ∈ range n, (1 - Polynomial.C ((X : R⟦X⟧) ^ (j + 1)) * Polynomial.X)

/-- The factor `j = 0` of the second product of `Φ n (n+1)` is `1 - u`. -/
private theorem Φ_eq (n : ℕ) : (Φ n (n + 1) : Polynomial R⟦X⟧) = (1 - Polynomial.X) * Ψ n := by
  simp only [Φ, Ψ, prod_range_succ' (fun j => (1 - Polynomial.C ((X : R⟦X⟧) ^ j) * Polynomial.X)),
    pow_zero, map_one, one_mul]
  ring

/-- `Ψ n (1) = (-1)^n (q;q)_n^2`. -/
private theorem eval_Ψ (n : ℕ) : (Ψ n : Polynomial R⟦X⟧).eval 1 = (-1) ^ n * qp n * qp n := by
  simp only [Ψ, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, mul_one, qp]
  rw [show (∏ i ∈ range n, ((X : R⟦X⟧) ^ (i + 1) - 1)) =
      ∏ i ∈ range n, ((-1) * (1 - X ^ (i + 1))) from prod_congr rfl (fun _ _ => by ring),
    prod_mul_distrib, prod_const, card_range]

/-- `Φ n (n+1)` has degree at most `2n+1`. -/
private theorem natDegree_Φ (n : ℕ) : (Φ n (n + 1) : Polynomial R⟦X⟧).natDegree < 2 * n + 2 := by
  have : (Φ n (n + 1) : Polynomial R⟦X⟧).natDegree ≤ 2 * n + 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_Φ, cf, if_neg (by omega)]
  omega

/-- Differentiating `Φ n (n+1) = (1-u) Ψ n` at `u = 1`:
`-(-1)^n (q;q)_n^2 = ∑_i i · cf n (n+1) i`. -/
private theorem deriv_identity (n : ℕ) :
    -((-1) ^ n * qp n * qp n : R⟦X⟧) =
      ∑ i ∈ range (2 * n + 2), cf n (n + 1) i * (i : R⟦X⟧) := by
  have h1 : (Polynomial.derivative (Φ n (n + 1) : Polynomial R⟦X⟧)).eval 1 =
      -((-1) ^ n * qp n * qp n) := by
    rw [Φ_eq, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, eval_Ψ]
    simp
  have h2 : (Polynomial.derivative (Φ n (n + 1) : Polynomial R⟦X⟧)).eval 1 =
      ∑ i ∈ range (2 * n + 2), cf n (n + 1) i * (i : R⟦X⟧) := by
    rw [Polynomial.derivative_eval, Polynomial.sum_over_range' _ (by simp) _ (natDegree_Φ n)]
    simp [coeff_Φ]
  rw [← h1, h2]

/-- `(q;q)_m ≡ (q;q)_k` modulo `q^{k+1}` for `k ≤ m`. -/
private theorem qp_cg {k m : ℕ} (h : k ≤ m) : Cg (k + 1) (qp m : R⟦X⟧) (qp k) := by
  induction m, h using Nat.le_induction with
  | base => exact Cg.rfl'
  | succ m hkm ih =>
    rw [qp_succ]
    have : Cg (k + 1) ((1 : R⟦X⟧) - X ^ (m + 1)) 1 := by
      unfold Cg; rw [sub_sub_cancel_left]; exact (dvd_neg).2 (pow_dvd_pow _ (by omega))
    have := ih.mul this; rwa [mul_one] at this

/-- `(q;q)_m / (q;q)_k ≡ 1` modulo `q^{k+1}` for `k ≤ m`. -/
private theorem qp_qpi_cg {k m : ℕ} (h : k ≤ m) : Cg (k + 1) ((qp m : R⟦X⟧) * qpi k) 1 := by
  have := (qp_cg (R := R) h).mul (Cg.rfl' (f := qpi k)); rwa [qp_mul_qpi] at this

/-- If `s + l = 2n+1`, `s ≤ n` and `n ≤ e + s`, then `q^e G(s,l) (q;q)_n ≡ q^e` modulo `q^{n+1}`. -/
private theorem key_cg {s l n e : ℕ} (hsl : s + l = 2 * n + 1) (hs : s ≤ n) (he : n ≤ e + s) :
    Cg (n + 1) ((X : R⟦X⟧) ^ e * (gb s l * qp n)) (X ^ e) := by
  have h1 : Cg (s + 1) ((qp (s + l) : R⟦X⟧) * qpi l) 1 := (qp_qpi_cg (by omega)).mono (by omega)
  have h2 : Cg (s + 1) ((qp n : R⟦X⟧) * qpi s) 1 := qp_qpi_cg hs
  have h3 := (h1.mul h2).X_pow_mul e
  rw [mul_one, mul_one] at h3
  have : (gb s l : R⟦X⟧) * qp n = qp (s + l) * qpi l * (qp n * qpi s) := by unfold gb; ring
  rw [this]
  exact h3.mono (by omega)

/-- Each term of `deriv_identity`, multiplied by `(q;q)_n`, is `(-1)^i i q^{ex n i}` modulo
`q^{n+1}`. -/
private theorem term_cg (n i : ℕ) (hi : i < 2 * n + 2) :
    Cg (n + 1) (cf n (n + 1) i * (i : R⟦X⟧) * qp n) ((-1) ^ i * (i : R⟦X⟧) * X ^ (ex n i)) := by
  have hc : cf n (n + 1) i * (i : R⟦X⟧) * qp n =
      (-1) ^ i * (i : R⟦X⟧) * (X ^ (ex n i) * (gb i (n + (n + 1) - i) * qp n)) := by
    rw [cf, if_pos (by omega)]; ring
  rw [hc]
  refine Cg.rfl'.mul ?_
  by_cases hin : i ≤ n
  · refine key_cg (by omega) hin ?_
    have : ex n i = tri (n - i) := by rw [ex, if_neg (by omega)]
    rw [this]; have := le_tri (n - i); omega
  · rw [gb_comm]
    refine key_cg (by omega) (by omega) ?_
    have : ex n i = tri (i - n - 1) := by rw [ex, if_pos (by omega)]
    rw [this]; have := le_tri (i - n - 1); omega

/-- The truncated Jacobi series `∑_{k ≤ n} (-1)^k (2k+1) q^{k(k+1)/2}`. -/
private noncomputable def J (n : ℕ) : R⟦X⟧ :=
  ∑ k ∈ range (n + 1), (-1) ^ k * (2 * (k : R⟦X⟧) + 1) * X ^ (tri k)

/-- Pairing the terms `i = n - k` and `i = n + 1 + k`. -/
private theorem pairing (n : ℕ) :
    ∑ i ∈ range (2 * n + 2), (-1) ^ i * (i : R⟦X⟧) * X ^ (ex n i) = (-1) ^ (n + 1) * J n := by
  rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring, sum_range_add,
    ← sum_range_reflect (fun i => (-1) ^ i * (i : R⟦X⟧) * X ^ (ex n i)) (n + 1), J, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by rw [mem_range] at hk; omega
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  have e1 : ex (k + d) (k + d + 1 - 1 - k) = tri k := by
    rw [ex, if_neg (by omega)]; congr 1; omega
  have e2 : ex (k + d) (k + d + 1 + k) = tri k := by
    rw [ex, if_pos (by omega)]; congr 1; omega
  rw [e1, e2, show k + d + 1 - 1 - k = d by omega]
  have s1 : (-1 : R⟦X⟧) ^ (k + d + 1 + k) = (-1) ^ (d + 1) := by
    rw [show k + d + 1 + k = (d + 1) + 2 * k by ring, pow_add, pow_mul, neg_one_sq, one_pow,
      mul_one]
  have s2 : (-1 : R⟦X⟧) ^ (k + d + 1) * (-1) ^ k = (-1) ^ (d + 1) := by
    rw [← pow_add, show k + d + 1 + k = (d + 1) + 2 * k by ring, pow_add, pow_mul, neg_one_sq,
      one_pow, mul_one]
  rw [s1]
  push_cast
  linear_combination (-(2 * (k : R⟦X⟧) + 1) * X ^ tri k) * s2

/-- **Jacobi's identity, truncated**: `(q;q)_n^3 ≡ ∑_{k ≤ n} (-1)^k (2k+1) q^{T(k)}` modulo
`q^{n+1}`. -/
private theorem jacobi_cg (n : ℕ) : Cg (n + 1) ((qp n : R⟦X⟧) ^ 3) (J n) := by
  have hsum : Cg (n + 1) ((∑ i ∈ range (2 * n + 2), cf n (n + 1) i * (i : R⟦X⟧)) * qp n)
      (∑ i ∈ range (2 * n + 2), (-1) ^ i * (i : R⟦X⟧) * X ^ (ex n i)) := by
    rw [sum_mul]
    exact Cg.sum _ fun i hi => term_cg n i (mem_range.1 hi)
  rw [← deriv_identity, pairing] at hsum
  have h := (Cg.rfl' (f := (-1 : R⟦X⟧) ^ (n + 1))).mul hsum
  have hsq : ((-1 : R⟦X⟧) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have e1 : (-1 : R⟦X⟧) ^ (n + 1) * (-((-1) ^ n * qp n * qp n) * qp n) = qp n ^ 3 := by
    rw [pow_succ]; linear_combination (qp n ^ 3) * hsq
  have e2 : (-1 : R⟦X⟧) ^ (n + 1) * ((-1) ^ (n + 1) * J n) = J n := by
    rw [pow_succ]; linear_combination (J n) * hsq
  rwa [e1, e2] at h



/-- The partition generating function `∑ p(n) q^n`. -/
private noncomputable def Pgf : R⟦X⟧ := PowerSeries.mk fun n => ((p n : ℕ) : R)

/-- `∑ pb(n, m) q^n = ∏_{j ≤ m} 1/(1 - q^j)`. -/
private noncomputable def pbS (m : ℕ) : R⟦X⟧ := PowerSeries.mk fun n => ((pb n m : ℕ) : R)

/-- `∑ pb(n,0) q^n = 1`. -/
private theorem pbS_zero : (pbS 0 : R⟦X⟧) = 1 := by
  ext n; rw [pbS, coeff_mk, pb_zero_right, coeff_one]; split_ifs <;> simp

/-- `(1 - q^{m+1}) ∑ pb(n,m+1) q^n = ∑ pb(n,m) q^n`, from `pb_succ`. -/
private theorem pbS_succ (m : ℕ) : (pbS (m + 1) : R⟦X⟧) * (1 - X ^ (m + 1)) = pbS m := by
  ext n
  rw [mul_sub, mul_one, map_sub, mul_comm, coeff_X_pow_mul']
  simp only [pbS, coeff_mk]
  rw [pb_succ n m]
  split_ifs <;> push_cast <;> ring

/-- `(∑ pb(n,m) q^n) (q;q)_m = 1`. -/
private theorem pbS_mul_qp (m : ℕ) : (pbS m : R⟦X⟧) * qp m = 1 := by
  induction m with
  | zero => rw [pbS_zero, qp_zero, one_mul]
  | succ m ih =>
    calc (pbS (m + 1) : R⟦X⟧) * qp (m + 1) = (pbS (m + 1) * (1 - X ^ (m + 1))) * qp m := by
          rw [qp_succ]; ring
      _ = 1 := by rw [pbS_succ, ih]

/-- `pb n m = pb n n` for `m ≥ n`. -/
private theorem pb_stable {n m : ℕ} (h : n ≤ m) : pb n m = pb n n := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => rw [pb_succ, if_neg (by omega), add_zero, ih]

/-- `P ≡ ∑ pb(n,N) q^n` modulo `q^{N+1}`. -/
private theorem Pgf_cg (N : ℕ) : Cg (N + 1) (Pgf : R⟦X⟧) (pbS N) :=
  cg_of_coeff fun i hi => by
    simp only [Pgf, pbS, coeff_mk, p_eq_pb, pb_stable (show i ≤ N by omega)]

/-- `P (q;q)_N ≡ 1` modulo `q^{N+1}`. -/
private theorem Pgf_qp_cg (N : ℕ) : Cg (N + 1) ((Pgf : R⟦X⟧) * qp N) 1 := by
  have := (Pgf_cg (R := R) N).mul (Cg.rfl' (f := qp N)); rwa [pbS_mul_qp] at this

/-- `J_N P^3 ≡ 1` modulo `q^{N+1}` (Jacobi's identity and the partition generating function). -/
private theorem J_Pgf_cg (N : ℕ) : Cg (N + 1) (J N * (Pgf : R⟦X⟧) ^ 3) 1 := by
  have h1 := ((jacobi_cg (R := R) N).symm).mul (Cg.rfl' (f := (Pgf : R⟦X⟧) ^ 3))
  have h2 := (Pgf_qp_cg (R := R) N).pow 3
  rw [one_pow] at h2
  refine h1.trans ?_
  rw [← mul_pow, mul_comm]; exact h2

/-- The coefficient of `q^n` in `F^k` as a sum over `k`-tuples summing to `n`. -/
private theorem coeff_pow_tuple (F : R⟦X⟧) (k n : ℕ) :
    coeff n (F ^ k) = ∑ f ∈ Finset.Nat.antidiagonalTuple k n, ∏ i, coeff (f i) F := by
  have : F ^ k = ∏ _i : Fin k, F := by simp
  rw [this, coeff_prod, ← Finset.piAntidiag_univ_fin_eq_antidiagonalTuple, finsuppAntidiag,
    sum_map]
  exact sum_attach (univ.piAntidiag n) (fun f => ∏ i, coeff (f i) F)


/-- Evaluate a coefficient list at `y`. -/
private def ev (y : R) : Poly → R
  | [] => 0
  | a :: l => (a : R) + y * ev y l

/-- Evaluation of the empty list. -/
@[simp] private theorem ev_nil (y : R) : ev y [] = 0 := rfl
/-- Evaluation of a cons. -/
@[simp] private theorem ev_cons (y : R) (a : ℤ) (l : Poly) : ev y (a :: l) = a + y * ev y l := rfl

/-- `padd` is addition of polynomials. -/
private theorem ev_padd (y : R) : ∀ p q : Poly, ev y (padd p q) = ev y p + ev y q
  | [], q => by simp [padd]
  | a :: p, [] => by simp [padd]
  | a :: p, b :: q => by simp only [padd, ev_cons, ev_padd y p q]; push_cast; ring

/-- `pscale` is multiplication by a constant. -/
private theorem ev_pscale (y : R) (c : ℤ) : ∀ p : Poly, ev y (pscale c p) = c * ev y p
  | [] => by simp [pscale]
  | a :: p => by
    have := ev_pscale y c p
    simp only [pscale, List.map_cons] at this ⊢
    rw [ev_cons, ev_cons, this]; push_cast; ring

/-- `pmul` is multiplication of polynomials. -/
private theorem ev_pmul (y : R) : ∀ p q : Poly, ev y (pmul p q) = ev y p * ev y q
  | [], q => by simp [pmul]
  | a :: p, q => by
    rw [pmul, ev_padd, ev_pscale, ev_cons, ev_cons, ev_pmul y p q]; push_cast; ring

/-- A `foldl` of `padd` is a sum. -/
private theorem ev_foldl_padd (y : R) (f : ℕ → Poly) : ∀ (l : List ℕ) (s : Poly),
    ev y (l.foldl (fun s j => padd s (f j)) s) = ev y s + (l.map fun j => ev y (f j)).sum
  | [], s => by simp
  | j :: l, s => by
    rw [List.foldl_cons, ev_foldl_padd y f l, ev_padd, List.map_cons, List.sum_cons]; ring

/-- A sum over `List.range` is a `Finset.range` sum. -/
private theorem list_range_sum (g : ℕ → R) (n : ℕ) :
    ((List.range n).map g).sum = ∑ j ∈ range n, g j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The power series whose coefficients are the evaluated entries of a list. -/
private noncomputable def evS (y : R) (A : Ser) : R⟦X⟧ := PowerSeries.mk fun i => ev y (A.getD i [])

/-- Coefficients of `evS`. -/
@[simp] private theorem coeff_evS (y : R) (A : Ser) (i : ℕ) :
    coeff i (evS y A) = ev y (A.getD i []) := coeff_mk _ _

/-- `mulCoeff A B i` is the coefficient of `x^i` in the product. -/
private theorem ev_mulCoeff (y : R) (A B : Ser) (i : ℕ) :
    ev y (mulCoeff A B i) = coeff i (evS y A * evS y B) := by
  rw [mulCoeff, ev_foldl_padd y (fun j => pmul (A.getD j []) (B.getD (i - j) [])), ev_nil,
    zero_add, list_range_sum, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j k => coeff j (evS y A) * coeff k (evS y B))]
  simp [ev_pmul]

/-- The entries of `smul L A B`. -/
private theorem getD_smul (L : ℕ) (A B : Ser) (i : ℕ) :
    (smul L A B).getD i [] = if i < L then mulCoeff A B i else [] := by
  rw [smul, List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_range h]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-- `smul L` is the product modulo `x^L`. -/
private theorem cg_smul (y : R) (L : ℕ) (A B : Ser) :
    Cg L (evS y (smul L A B)) (evS y A * evS y B) :=
  cg_of_coeff fun i hi => by rw [coeff_evS, getD_smul, if_pos hi, ev_mulCoeff]

/-- One more step of the loop in `sinv`. -/
private theorem sinv_succ (L : ℕ) (A : Ser) : sinv (L + 1) A = sinv L A ++ [if L = 0 then [1] else
    pscale (-1) ((List.range L).foldl
      (fun s j => padd s (pmul (A.getD (j + 1) []) ((sinv L A).getD (L - 1 - j) []))) [])] := by
  simp only [sinv, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `sinv L A` has length `L`. -/
private theorem length_sinv (L : ℕ) (A : Ser) : (sinv L A).length = L := by
  induction L with
  | zero => rfl
  | succ L ih => rw [sinv_succ, List.length_append, ih]; rfl

/-- The entries of `sinv` are stable once computed. -/
private theorem getD_sinv_of_lt {L M : ℕ} (h : L ≤ M) (A : Ser) {i : ℕ} (hi : i < L) :
    (sinv M A).getD i [] = (sinv L A).getD i [] := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ M hLM ih =>
    rw [sinv_succ, List.getD_append _ _ _ _ (by rw [length_sinv]; omega), ih]

/-- The recursion satisfied by the entries of `sinv L A`. -/
private theorem ev_sinv (y : R) (A : Ser) {L i : ℕ} (hi : i < L) :
    ev y ((sinv L A).getD i []) = if i = 0 then 1 else
      -∑ j ∈ range i, ev y (A.getD (j + 1) []) * ev y ((sinv L A).getD (i - 1 - j) []) := by
  rw [getD_sinv_of_lt (show i + 1 ≤ L by omega) A (Nat.lt_succ_self i), sinv_succ,
    List.getD_append_right _ _ _ _ (by rw [length_sinv]), length_sinv, Nat.sub_self]
  split_ifs with h0
  · simp
  · simp only [List.getD_cons_zero]
    rw [ev_pscale,
      ev_foldl_padd y (fun j => pmul (A.getD (j + 1) []) ((sinv i A).getD (i - 1 - j) [])),
      ev_nil, zero_add, list_range_sum, Int.cast_neg, Int.cast_one, neg_one_mul]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [ev_pmul, getD_sinv_of_lt (show i ≤ L by omega) A (show i - 1 - j < i by omega)]

/-- `A · sinv L A ≡ 1` modulo `x^L` when `A` has constant term `1`. -/
private theorem sinv_spec (y : R) (A : Ser) (hA : ev y (A.getD 0 []) = 1) (L : ℕ) :
    Cg L (evS y A * evS y (sinv L A)) 1 := by
  refine cg_of_coeff fun i hi => ?_
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => coeff j (evS y A) * coeff k (evS y (sinv L A))), sum_range_succ', coeff_one]
  simp only [coeff_evS, Nat.sub_zero, hA, one_mul]
  rw [ev_sinv y A hi]
  split_ifs with h0
  · subst h0; simp
  · rw [add_neg_eq_zero]
    refine sum_congr rfl fun j hj => ?_
    rw [show i - (j + 1) = i - 1 - j by omega]

/-- `sinv L A` agrees with any inverse of `A` modulo `x^L`. -/
private theorem sinv_inv (y : R) (A : Ser) (hA : ev y (A.getD 0 []) = 1) (L : ℕ) (W : R⟦X⟧)
    (hW : evS y A * W = 1) : Cg L (evS y (sinv L A)) W := by
  have h := (sinv_spec y A hA L).mul (Cg.rfl' (f := W))
  rw [one_mul, mul_comm (evS y A), mul_assoc, hW, mul_one] at h
  exact h


/-- One step of the loop in `thetaCoeff`. -/
private def thStep (B : Ser) (m : ℕ) (st : Poly × Ser × Ser) (n : ℕ) : Poly × Ser × Ser :=
  if n * (n + 1) / 2 ≤ m then
    (padd st.1 (pscale ((-1) ^ n)
        (padd (st.2.1.getD (m - n * (n + 1) / 2) [])
          (pscale (-1) (st.2.2.getD (m - n * (n + 1) / 2) [])))),
      smul (m + 1) st.2.1 B, smul (m + 1) st.2.2 (sinv (m + 1) B))
  else st

/-- The state of the loop in `thetaCoeff` after `k` steps. -/
private def thSt (B : Ser) (m k : ℕ) : Poly × Ser × Ser :=
  (List.range k).foldl (thStep B m) ([], [[1]], sinv (m + 1) B)

/-- `thetaCoeff` in terms of `thSt`. -/
private theorem thetaCoeff_eq (B : Ser) (m : ℕ) : thetaCoeff B m = (thSt B m (m + 1)).1 := rfl

/-- One more step of the loop in `thetaCoeff`. -/
private theorem thSt_succ (B : Ser) (m k : ℕ) : thSt B m (k + 1) = thStep B m (thSt B m k) k := by
  simp only [thSt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The list `[[1]]` is the series `1`. -/
private theorem evS_one (y : R) : evS y [[1]] = 1 := by
  ext i
  rw [coeff_evS, coeff_one]
  rcases i with _ | i
  · simp
  · simp

/-- `T(k-1) ≤ T(k)`. -/
private theorem tri_mono_aux (k : ℕ) : (k - 1) * k / 2 ≤ tri k :=
  Nat.div_le_div_right (Nat.mul_le_mul (Nat.sub_le k 1) (Nat.le_succ k))

/-- The loop invariant of `thetaCoeff`: the partial sum, and (while the loop is active) the powers
`B^k` and `B^{-(k+1)}` modulo `x^{m+1}`. -/
private theorem th_inv (y : R) (B : Ser) (m : ℕ) (W : R⟦X⟧)
    (hW : Cg (m + 1) (evS y (sinv (m + 1) B)) W) (k : ℕ) :
    ev y (thSt B m k).1 = ∑ n ∈ range k, (if tri n ≤ m then
      (-1) ^ n * (coeff (m - tri n) (evS y B ^ n) - coeff (m - tri n) (W ^ (n + 1))) else 0) ∧
    ((k - 1) * k / 2 ≤ m → Cg (m + 1) (evS y (thSt B m k).2.1) (evS y B ^ k) ∧
      Cg (m + 1) (evS y (thSt B m k).2.2) (W ^ (k + 1))) := by
  induction k with
  | zero =>
    refine ⟨by simp [thSt], fun _ => ⟨?_, ?_⟩⟩
    · simp only [thSt, List.range_zero, List.foldl_nil, pow_zero, evS_one]; exact Cg.rfl'
    · simpa [thSt] using hW
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [thSt_succ, thStep, sum_range_succ]
    by_cases h : tri k ≤ m
    · have h' : k * (k + 1) / 2 ≤ m := h
      rw [if_pos h', if_pos h]
      obtain ⟨c1, c2⟩ := ih2 ((tri_mono_aux k).trans h)
      refine ⟨?_, fun _ => ⟨?_, ?_⟩⟩
      · simp only
        rw [ev_padd, ev_pscale, ev_padd, ev_pscale, ih1, ← coeff_evS, ← coeff_evS,
          show k * (k + 1) / 2 = tri k from rfl, c1.coeff_eq (show m - tri k < m + 1 by omega),
          c2.coeff_eq (show m - tri k < m + 1 by omega)]
        push_cast
        ring
      · rw [pow_succ]; exact (cg_smul y _ _ _).trans (c1.mul Cg.rfl')
      · rw [pow_succ]; exact (cg_smul y _ _ _).trans (c2.mul hW)
    · have h' : ¬ k * (k + 1) / 2 ≤ m := h
      rw [if_neg h', if_neg h, add_zero]
      refine ⟨ih1, fun hk => absurd ?_ h⟩
      have : (k + 1 - 1) * (k + 1) / 2 = tri k := by simp [tri]
      omega

/-- `∑_{n ≤ m} (-1)^n q^{n(n+1)/2} (V^n - W^{n+1})`. -/
private noncomputable def Θ (V W : R⟦X⟧) (m : ℕ) : R⟦X⟧ :=
  ∑ n ∈ range (m + 1), (-1) ^ n * X ^ (tri n) * (V ^ n - W ^ (n + 1))

/-- Semantics of `thetaCoeff`: it is the coefficient of `x^m` in `Θ B B⁻¹ m`. -/
private theorem ev_thetaCoeff (y : R) (B : Ser) (m : ℕ) (W : R⟦X⟧) (hB : ev y (B.getD 0 []) = 1)
    (hW : evS y B * W = 1) : ev y (thetaCoeff B m) = coeff m (Θ (evS y B) W m) := by
  rw [thetaCoeff_eq, (th_inv y B m W (sinv_inv y B hB (m + 1) W hW) (m + 1)).1, Θ, map_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [show ((-1 : R⟦X⟧)) ^ n = C ((-1 : R) ^ n) by simp, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', map_sub]
  split_ifs <;> simp

/-- Unfolding `coeffs`. -/
private theorem coeffs_succ (m : ℕ) : coeffs (m + 1) = coeffs m ++
    [padd (0 :: (coeffs m).getD m []) (pscale (-1) (thetaCoeff (coeffs m) (m + 1)))] := rfl

/-- `coeffs m` has length `m + 1`. -/
private theorem length_coeffs (m : ℕ) : (coeffs m).length = m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [coeffs_succ, List.length_append, ih]; rfl

/-- The entries of `coeffs` are stable once computed. -/
private theorem getD_coeffs_of_le {j M : ℕ} (h : j ≤ M) :
    (coeffs M).getD j [] = (coeffs j).getD j [] := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ M hjM ih =>
    rw [coeffs_succ, List.getD_append _ _ _ _ (by rw [length_coeffs]; omega), ih]

/-- Entries of `coeffs m` beyond `m` are empty. -/
private theorem getD_coeffs_of_gt {j m : ℕ} (h : m < j) : (coeffs m).getD j [] = [] :=
  List.getD_eq_default _ _ (by rw [length_coeffs]; omega)

/-- `a_j`, the coefficient of `x^j` of the computed series, evaluated at `y`. -/
private def aco (y : R) (j : ℕ) : R := ev y ((coeffs j).getD j [])

/-- The series of `coeffs m` is the truncation of the computed series. -/
private theorem coeff_evS_coeffs (y : R) (m j : ℕ) :
    coeff j (evS y (coeffs m)) = if j ≤ m then aco y j else 0 := by
  rw [coeff_evS]
  split_ifs with h
  · rw [getD_coeffs_of_le h]; rfl
  · rw [getD_coeffs_of_gt (by omega)]; rfl

/-- `a_0 = 1`. -/
private theorem aco_zero (y : R) : aco y 0 = 1 := by simp [aco, coeffs]

/-- The recursion `a_{m+1} = y a_m - [x^{m+1}] F(a_0 + ⋯ + a_m x^m)`. -/
private theorem aco_succ (y : R) (m : ℕ) :
    aco y (m + 1) = y * aco y m - ev y (thetaCoeff (coeffs m) (m + 1)) := by
  rw [aco, coeffs_succ, List.getD_append_right _ _ _ _ (by rw [length_coeffs]), length_coeffs,
    Nat.sub_self, List.getD_cons_zero, ev_padd, ev_cons, ev_pscale, aco]
  push_cast; ring


/-- If `X^M ∣ D` then `[x^M] (F D) = F(0) · [x^M] D`. -/
private theorem coeff_mul_of_dvd {M : ℕ} (F : R⟦X⟧) {D : R⟦X⟧} (h : (X : R⟦X⟧) ^ M ∣ D) :
    coeff M (F * D) = constantCoeff F * coeff M D := by
  obtain ⟨D', rfl⟩ := h
  rw [mul_left_comm, coeff_X_pow_mul', if_pos le_rfl, coeff_X_pow_mul', if_pos le_rfl,
    Nat.sub_self, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul]

/-- Replacing the full solution `E` by its truncation `V` (agreeing below `x^M`, zero at `x^M`)
changes `[x^M] Θ` by `-[x^M] E`. -/
private theorem pert {V E W Eb : R⟦X⟧} {M : ℕ} (hVW : V * W = 1) (hEEb : E * Eb = 1)
    (hV0 : constantCoeff V = 1) (hEb0 : constantCoeff Eb = 1) (hVE : Cg M V E)
    (hVM : coeff M V = 0) :
    coeff M (Θ V W M) = coeff M (Θ E Eb M) - coeff M E := by
  have hWEb : Cg M W Eb := by
    have h := (Cg.rfl' (f := W)).mul (hVE.symm.mul (Cg.rfl' (f := Eb)))
    rw [hEEb, mul_one, ← mul_assoc, mul_comm W V, hVW, one_mul] at h
    exact h
  have hdiff : Θ V W M - Θ E Eb M = ∑ n ∈ range M, (-1) ^ (n + 1) * X ^ (tri (n + 1)) *
      ((V ^ (n + 1) - E ^ (n + 1)) - (W ^ (n + 1 + 1) - Eb ^ (n + 1 + 1))) + (Eb - W) := by
    rw [Θ, Θ, ← sum_sub_distrib, sum_range_succ']
    congr 1
    · exact sum_congr rfl fun n _ => by ring
    · simp [tri]
  have hzero : Cg (M + 1) (∑ n ∈ range M, (-1) ^ (n + 1) * X ^ (tri (n + 1)) *
      ((V ^ (n + 1) - E ^ (n + 1)) - (W ^ (n + 1 + 1) - Eb ^ (n + 1 + 1)))) 0 := by
    rw [← sum_const_zero (s := range M)]
    refine Cg.sum _ fun n _ => ?_
    have h1 : Cg M ((V ^ (n + 1) - E ^ (n + 1)) - (W ^ (n + 1 + 1) - Eb ^ (n + 1 + 1))) 0 := by
      have := ((hVE.pow (n + 1)).sub (Cg.rfl' (f := E ^ (n + 1)))).sub
        ((hWEb.pow (n + 1 + 1)).sub (Cg.rfl' (f := Eb ^ (n + 1 + 1))))
      simpa using this
    have h2 := h1.X_pow_mul (tri (n + 1))
    rw [mul_zero] at h2
    have h3 := (Cg.rfl' (f := ((-1 : R⟦X⟧)) ^ (n + 1))).mul
      (h2.mono (show M + 1 ≤ M + tri (n + 1) by have := le_tri (n + 1); omega))
    rw [mul_zero, ← mul_assoc] at h3
    exact h3
  have hc1 : coeff M (Θ V W M) - coeff M (Θ E Eb M) = coeff M (Eb - W) := by
    rw [← map_sub, hdiff, map_add, hzero.coeff_eq (Nat.lt_succ_self M), map_zero, zero_add]
  have hc2 : coeff M (W - Eb) = coeff M E := by
    have h0 : V * (W - Eb) + (V - E) * Eb = 0 := by linear_combination hVW - hEEb
    have h1 := congrArg (coeff M) h0
    rw [map_add, coeff_mul_of_dvd V hWEb, mul_comm (V - E), coeff_mul_of_dvd Eb hVE, hV0, hEb0,
      map_sub, map_sub, hVM, map_zero] at h1
    rw [map_sub]
    linear_combination h1
  rw [map_sub] at hc1 hc2
  linear_combination hc1 - hc2

/-- If `w^3 = 0` then `(1+w)^n - (1-w+w^2)^{n+1} = (2n+1)(w - w^2)`. -/
private theorem pow_sub_pow_of_cube {S : Type*} [CommRing S] (w : S) (hw : w ^ 3 = 0) (n : ℕ) :
    (1 + w) ^ n - (1 - w + w ^ 2) ^ (n + 1) = (2 * (n : S) + 1) * (w - w ^ 2) := by
  have h1 : ∀ n : ℕ, (1 + w) ^ n = 1 + n * w + (n.choose 2 : S) * w ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, Nat.choose_succ_succ', Nat.choose_one_right]
      push_cast
      linear_combination (n.choose 2 : S) * hw
  have h2 : ∀ n : ℕ, (1 - w + w ^ 2) ^ n = 1 - n * w + (n + n.choose 2 : S) * w ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, Nat.choose_succ_succ', Nat.choose_one_right]
      push_cast
      linear_combination (-(n : S) - (n + n.choose 2 : S) + (n + n.choose 2 : S) * w) * hw
  rw [h1, h2, Nat.choose_succ_succ', Nat.choose_one_right]
  push_cast
  ring

section Solution
variable (y : R)

/-- `u = x P(x)^3`. -/
private noncomputable def U : R⟦X⟧ := X * Pgf ^ 3

/-- `w = y u + 2 y^2 u^2`. -/
private noncomputable def wS : R⟦X⟧ := C y * U + C (2 * y ^ 2) * U ^ 2

/-- The solution mod `y^3`: `E = 1 + y u + 2 y^2 u^2`. -/
private noncomputable def Ecal : R⟦X⟧ := 1 + wS y

/-- Its inverse mod `y^3`. -/
private noncomputable def Ebar : R⟦X⟧ := 1 - wS y + wS y ^ 2

variable {y}

/-- `w^3 = 0` since `y^3 = 0`. -/
private theorem wS_cube (hy : y ^ 3 = 0) : wS y ^ 3 = 0 := by
  have : wS y = C y * (U + C (2 * y) * U ^ 2) := by simp only [wS, map_mul, map_pow]; ring
  rw [this, mul_pow, ← map_pow, hy, map_zero, zero_mul]

/-- `E · E⁻¹ = 1`. -/
private theorem Ecal_mul_Ebar (hy : y ^ 3 = 0) : Ecal y * Ebar y = 1 := by
  simp only [Ecal, Ebar]; linear_combination wS_cube hy

/-- `w` has constant coefficient `0`. -/
private theorem constantCoeff_wS : constantCoeff (wS y) = 0 := by
  simp [wS, U]

/-- `E⁻¹` has constant coefficient `1`. -/
private theorem constantCoeff_Ebar : constantCoeff (Ebar y) = 1 := by
  simp [Ebar, constantCoeff_wS]

/-- `w - w^2 = y u + y^2 u^2` since `y^3 = 0`. -/
private theorem wS_sub_sq (hy : y ^ 3 = 0) : wS y - wS y ^ 2 = C y * U + C (y ^ 2) * U ^ 2 := by
  have hy4 : y ^ 4 = 0 := by rw [pow_succ, hy, zero_mul]
  have e3 : (C (y ^ 3) : R⟦X⟧) = 0 := by rw [hy, map_zero]
  have e4 : (C (y ^ 4) : R⟦X⟧) = 0 := by rw [hy4, map_zero]
  simp only [wS, map_mul, map_pow, map_ofNat] at e3 e4 ⊢
  linear_combination (-4 * U ^ 3 : R⟦X⟧) * e3 + (-4 * U ^ 4 : R⟦X⟧) * e4

/-- For `E`, `Θ E E⁻¹ M = J_M (y u + y^2 u^2)`. -/
private theorem Θ_E (hy : y ^ 3 = 0) (M : ℕ) :
    Θ (Ecal y) (Ebar y) M = J M * (C y * U + C (y ^ 2) * U ^ 2) := by
  rw [Θ, J, sum_mul, ← wS_sub_sq hy]
  refine sum_congr rfl fun n _ => ?_
  rw [Ecal, Ebar, pow_sub_pow_of_cube _ (wS_cube hy)]
  ring

/-- The functional equation for `E` at order `x^{m+1}`: `[x^{m+1}] F(E) = y [x^m] E`. -/
private theorem fe (hy : y ^ 3 = 0) (m : ℕ) :
    coeff (m + 1) (Θ (Ecal y) (Ebar y) (m + 1)) = y * coeff m (Ecal y) := by
  have h1 : Θ (Ecal y) (Ebar y) (m + 1) = (J (m + 1) * Pgf ^ 3) * (X * (C y + C (y ^ 2) * U)) := by
    rw [Θ_E hy, U]; ring
  have h2 : X * (C y + C (y ^ 2) * U) = X * (C y * Ecal y) := by
    have e3 : (C (y ^ 3) : R⟦X⟧) = 0 := by rw [hy, map_zero]
    simp only [Ecal, wS, map_mul, map_pow, map_ofNat] at e3 ⊢
    linear_combination (-2 * X * U ^ 2 : R⟦X⟧) * e3
  have h3 := (J_Pgf_cg (R := R) (m + 1)).mul (Cg.rfl' (f := X * (C y + C (y ^ 2) * U)))
  rw [one_mul, ← h1, h2] at h3
  rw [h3.coeff_eq (Nat.lt_succ_self (m + 1)), coeff_succ_X_mul, coeff_C_mul]

/-- Modulo `y^3`, the computed coefficients are those of `E = 1 + y u + 2 y^2 u^2`. -/
private theorem aco_eq (hy : y ^ 3 = 0) : ∀ m, aco y m = coeff m (Ecal y) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · rw [aco_zero, coeff_zero_eq_constantCoeff_apply, Ecal, map_add, constantCoeff_wS, map_one,
        add_zero]
    · have hB0 : ev y ((coeffs m).getD 0 []) = 1 := by
        rw [getD_coeffs_of_le (Nat.zero_le m)]; exact aco_zero y
      have hV0 : constantCoeff (evS y (coeffs m)) = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_evS, hB0]
      have hVW := mul_invOfUnit (evS y (coeffs m)) 1 (by rw [hV0]; rfl)
      have hVE : Cg (m + 1) (evS y (coeffs m)) (Ecal y) := cg_of_coeff fun i hi => by
        rw [coeff_evS_coeffs, if_pos (by omega), ih i (by omega)]
      have hVM : coeff (m + 1) (evS y (coeffs m)) = 0 := by
        rw [coeff_evS_coeffs, if_neg (by omega)]
      rw [aco_succ, ev_thetaCoeff y (coeffs m) (m + 1) _ hB0 hVW,
        pert hVW (Ecal_mul_Ebar hy) hV0 constantCoeff_Ebar hVE hVM, fe hy,
        ih m (by omega)]
      ring

end Solution


/-- `ℤ[y]/(y^3)`. -/
private abbrev R3 := Polynomial ℤ ⧸ Ideal.span {(Polynomial.X : Polynomial ℤ) ^ 3}

/-- The quotient map `ℤ[y] → ℤ[y]/(y^3)`. -/
private noncomputable def π3 : Polynomial ℤ →+* R3 := Ideal.Quotient.mk _

/-- `y^3 = 0` in `ℤ[y]/(y^3)`. -/
private theorem y3_cube : (π3 Polynomial.X) ^ 3 = 0 := by
  rw [← map_pow, π3, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- Evaluation commutes with ring homomorphisms. -/
private theorem ev_map {S : Type*} [CommRing S] (f : R →+* S) (y : R) :
    ∀ l : Poly, f (ev y l) = ev (f y) l
  | [] => by simp
  | a :: l => by simp [ev_map f y l]

/-- Evaluating a list at the variable `y` of `ℤ[y]` gives the polynomial with these coefficients. -/
private theorem coeff_evX : ∀ (l : Poly) (k : ℕ),
    (ev (Polynomial.X : Polynomial ℤ) l).coeff k = l.getD k 0
  | [], k => by simp
  | a :: l, 0 => by
    rw [ev_cons, Polynomial.coeff_add, Polynomial.intCast_coeff_zero, Polynomial.coeff_X_mul_zero,
      add_zero]; rfl
  | a :: l, k + 1 => by
    rw [ev_cons, Polynomial.coeff_add, ← Polynomial.C_eq_intCast, Polynomial.coeff_C,
      if_neg (Nat.succ_ne_zero k), Polynomial.coeff_X_mul, coeff_evX l k, zero_add]; rfl

/-- `P` over `ℤ[y]/(y^3)` is the image of `P` over `ℤ`. -/
private theorem Pgf_map : (Pgf : R3⟦X⟧) = map (Int.castRingHom R3) (Pgf : ℤ⟦X⟧) := by
  ext n; simp [Pgf]

/-- `u` over `ℤ[y]/(y^3)` is the image of `u` over `ℤ`. -/
private theorem U_map : (U : R3⟦X⟧) = map (Int.castRingHom R3) (U : ℤ⟦X⟧) := by
  simp [U, Pgf_map]

/-- Columns `1` and `2` of the triangle are the coefficients of `u = x P^3` and `2u^2`. -/
private theorem T_cols (n : ℕ) :
    T n 1 = coeff n (U : ℤ⟦X⟧) ∧ T n 2 = 2 * coeff n ((U : ℤ⟦X⟧) ^ 2) := by
  have h := aco_eq (R := R3) (y := π3 Polynomial.X) y3_cube n
  have hC : ∀ z : ℤ, π3 (Polynomial.C z) = (z : R3) := fun z => eq_intCast (π3.comp Polynomial.C) z
  set u := coeff n (U : ℤ⟦X⟧)
  set v := coeff n ((U : ℤ⟦X⟧) ^ 2)
  set Q : Polynomial ℤ := Polynomial.C (if n = 0 then 1 else 0) + Polynomial.C u * Polynomial.X +
    Polynomial.C (2 * v) * Polynomial.X ^ 2 with hQdef
  have e1 : coeff n (Ecal (π3 Polynomial.X)) = ((if n = 0 then 1 else 0 : ℤ) : R3) +
      π3 Polynomial.X * (u : R3) + 2 * (π3 Polynomial.X) ^ 2 * (v : R3) := by
    rw [Ecal, wS, map_add, map_add, coeff_one, coeff_C_mul, coeff_C_mul, U_map,
      ← map_pow (PowerSeries.map (Int.castRingHom R3)), coeff_map, coeff_map]
    simp only [Int.coe_castRingHom]
    split_ifs <;> simp <;> ring
  have e2 : π3 Q = ((if n = 0 then 1 else 0 : ℤ) : R3) +
      π3 Polynomial.X * (u : R3) + 2 * (π3 Polynomial.X) ^ 2 * (v : R3) := by
    rw [hQdef, map_add, map_add, map_mul, map_mul, hC, hC, hC, map_pow]
    push_cast; ring
  have hQ : π3 (ev Polynomial.X ((coeffs n).getD n [])) = π3 Q := by
    rw [ev_map, ← aco, h, e1, e2]
  have hdvd : (Polynomial.X : Polynomial ℤ) ^ 3 ∣ ev Polynomial.X ((coeffs n).getD n []) - Q := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]; exact hQ
  obtain ⟨r, hr⟩ := hdvd
  have hQ1 : Q.coeff 1 = u := by
    rw [hQdef, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
    simp
  have hQ2 : Q.coeff 2 = 2 * v := by
    rw [hQdef, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
    simp
  have c1 := congrArg (fun f => Polynomial.coeff f 1) hr
  have c2 := congrArg (fun f => Polynomial.coeff f 2) hr
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul', hQ1, hQ2] at c1 c2
  rw [if_neg (by norm_num)] at c1 c2
  rw [T, T, ← coeff_evX, ← coeff_evX]
  exact ⟨by linear_combination c1, by linear_combination c2⟩


/-- The coefficients of `P^j` count partitions into parts of `j` kinds. -/
private theorem coeff_Pgf_pow (j n : ℕ) :
    coeff n ((Pgf : ℤ⟦X⟧) ^ j) = (partitionsOfKinds j n : ℤ) := by
  rw [coeff_pow_tuple, partitionsOfKinds]
  push_cast
  simp [Pgf]

/-- **Hanna's conjectures (C.1) and (C.2) hold.** Column 1 of the triangle is A000716 and
column 2 is twice A023005. -/
theorem result : statement := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · rw [(T_cols (n + 1)).1, U, coeff_succ_X_mul, coeff_Pgf_pow, A000716]
  · rw [(T_cols (n + 2)).2, U, show ((X : ℤ⟦X⟧) * Pgf ^ 3) ^ 2 = X ^ 2 * Pgf ^ 6 by ring,
      coeff_X_pow_mul', if_pos (by omega), show n + 2 - 2 = n by omega, coeff_Pgf_pow, A023005]

end Math0.Frontier.A355360

#math0_settles Math0.Frontier.A355360.result Math0.Statements.A355360.statement
