/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A350499: Kurkov's recursion for the free cumulants

Source: https://oeis.org/A350499, _Mikhail Kurkov_, Mar 30 2025 (FORMULA section; the entry is by
_Tom Copeland_, Jan 01 2022, with terms `a(19)` and beyond by _Andrew Howroyd_). Verbatim:
> Conjecture: free cumulants in terms of the free moments are R(n,1) for n > 0 where
> R(n,k) = R(n-1,k+1) - Sum_{j=1..n-1} R(j,k)*R(n-j,1) for n > 1, k > 0 with R(1,k) = m_k for
> k > 0. - _Mikhail Kurkov_, Mar 30 2025

The entry's name: "Unsigned coefficients of free moment partition polynomials determining the free
cumulants from the free moments of free probability theory. Irregular triangle with row lengths
given by A000041, n >= 1." Comment: "Coefficients are listed in Abramowitz and Stegun order
(A036036)." Formula: "O.g.f.: C(x) = 1 + c_1 x + c_2 x^2 + ... = x / (x + m_1 x^2 + m_2 x^3 +
m_3 x^4 + ...)^(-1) = x / M^(-1)(x), the shifted reciprocal of the compositional inverse of a
power series M(x) = x + m_1 x^2 + m_2 x^3 + ..., the o.g.f. of the free moments m_n in free
probability theory." Offset `1`; data: 66 terms (rows `n = 1, …, 8`).

## Encoding

* *Moments.* The conjecture is an identity between polynomials in the free moments, so the
  moments are the indeterminates `m_k = MvPolynomial.X k` (`k ≥ 1`) of `ℤ[m_1, m_2, …] =
  MvPolynomial ℕ ℤ`, with the normalization `m_0 = 1` (`mom`). (This is the universal case: by
  evaluation it implies the identity for every sequence of moments in every commutative ring.)
* *Free cumulants*, following the entry's o.g.f.: `M(x) = x + m₁x² + m₂x³ + ⋯` (`M`); its
  compositional inverse `M^⟨-1⟩` is Mathlib's `PowerSeries.substInvOfIsUnit` (`Minv`; it is a
  two-sided inverse, `M_subst_Minv : M(M^⟨-1⟩(x)) = x` and `Minv_subst_M`); `C(x) = x / M^⟨-1⟩(x)`
  (`Cgf`) is defined as the inverse of the power series `M^⟨-1⟩(x)/x`, which has constant term `1`
  (so `Cgf_mul_Minv : C(x) · M^⟨-1⟩(x) = x`, which determines `C`); and the free cumulant
  `c_n = freeCumulant n` is the coefficient of `xⁿ` in `C(x)` (so `c_0 = 1`).
* *The triangle.* `T n k` (`n ≥ 1`, `0 ≤ k < p(n)`) is the absolute value of the coefficient, in
  `c_n`, of the monomial `m_λ = m_{λ₁} m_{λ₂} ⋯` of the `k`-th partition `λ` of `n` (counting from
  `0`) in Abramowitz–Stegun order. `asPartitions n` produces that order: by increasing number of
  parts, then in increasing lexicographic order of the weakly increasing lists of parts (the
  definition of A036036). It lists every partition of `n` exactly once (`mem_asPartitions`,
  `nodup_asPartitions`) and reproduces all 99 listed terms of A036036 (`asPartitions_A036036`).
* *Computing `T`.* `T` is computable: `c_n` is computed in a list representation of integer
  polynomials (`Poly`, with meaning `ev`) by the recursion `c_0 = 1`,
  `c_t = m_t - ∑_{n=1}^{t-1} c_n [x^(t-n)] P(x)^n`, where `P(x) = M(x)/x`. This recursion is the
  coefficient form of `C(M(x)) = M(x)/x` and is *derived* from the definitions above
  (`Cgf_subst_M`, `cumulant_moment`, `freeCumulant_succ`). `ev_cumPoly` proves that the computed
  list denotes `freeCumulant n`, and `T_eq_coeff` restates `T n k` as
  `|MvPolynomial.coeff λ (freeCumulant n)|`; so the computable `T` is provably the entry's
  definition. As a check of the signs, `cumulant_examples` reproduces the signed polynomials
  `c_1, …, c_5` shown in the entry's EXAMPLE section.
* *Data.* `a` is the triangle read by rows (offset `1`); `a_data` checks all 66 listed terms
  `a 1, …, a 66` in the kernel.
* *Kurkov's array* `R m n k` is defined for any commutative ring and moment sequence `m`;
  `R_one` and `R_rec` are the literal clauses `R(1,k) = m_k` and
  `R(n,k) = R(n-1,k+1) - ∑_{j=1}^{n-1} R(j,k) R(n-j,1)` (`n > 1`). The recursion only ever
  increases `k`, so starting from `k = 1` it uses only `k > 0` and `m_k` with `k > 0`, as in the
  entry; the values `R(0, k)` (junk, `0`) are never used for `n ≥ 1`.
* *The conjecture* (`statement`): for every `n > 0`, `R(n, 1) = c_n` in `ℤ[m_1, m_2, …]`, where
  `R` is built from `R(1, k) = m_k`.
-/

namespace Math0.Statements.A350499

open PowerSeries

/-! ### Free moments and free cumulants -/

/-- The free moments as polynomials over `ℤ` in the indeterminates `m_1, m_2, …`: `mom 0 = 1`
(normalization `m_0 = 1`) and `mom k = m_k = X k` for `k ≥ 1`. -/
noncomputable def mom (k : ℕ) : MvPolynomial ℕ ℤ := if k = 0 then 1 else MvPolynomial.X k

/-- The moment series `M(x) = x + m₁ x² + m₂ x³ + ⋯` (the coefficient of `x^(k+1)` is `m_k`). -/
noncomputable def M : PowerSeries (MvPolynomial ℕ ℤ) :=
  PowerSeries.mk fun i => if i = 0 then 0 else mom (i - 1)

theorem constantCoeff_M : constantCoeff M = 0 := by
  simp [M, ← coeff_zero_eq_constantCoeff_apply]

theorem coeff_one_M : coeff 1 M = 1 := by
  simp [M, mom]

theorem isUnit_coeff_one_M : IsUnit (coeff 1 M) := by
  rw [coeff_one_M]; exact isUnit_one

/-- The compositional inverse `M^⟨-1⟩` of `M` (Mathlib's `PowerSeries.substInvOfIsUnit`). -/
noncomputable def Minv : PowerSeries (MvPolynomial ℕ ℤ) :=
  M.substInvOfIsUnit isUnit_coeff_one_M

/-- `M(M^⟨-1⟩(x)) = x`. -/
theorem M_subst_Minv : M.subst Minv = X :=
  M.subst_substInvOfIsUnit_right constantCoeff_M isUnit_coeff_one_M

/-- `M^⟨-1⟩(M(x)) = x`. -/
theorem Minv_subst_M : Minv.subst M = X :=
  M.subst_substInvOfIsUnit_left constantCoeff_M isUnit_coeff_one_M

theorem constantCoeff_Minv : constantCoeff Minv = 0 :=
  M.constantCoeff_substInvOfIsUnit isUnit_coeff_one_M

theorem coeff_one_Minv : coeff 1 Minv = 1 := by
  rw [Minv, coeff_one_substInvOfIsUnit]
  have : isUnit_coeff_one_M.unit = 1 := Units.ext coeff_one_M
  rw [this, inv_one, Units.val_one]

/-- The generating function of the free cumulants, `C(x) = x / M^⟨-1⟩(x)`: writing
`M^⟨-1⟩(x) = x · Q(x)` with `Q(x) = 1 + q₁ x + ⋯`, it is `C = Q⁻¹`. -/
noncomputable def Cgf : PowerSeries (MvPolynomial ℕ ℤ) :=
  invOfUnit (PowerSeries.mk fun n => coeff (n + 1) Minv) 1

/-- `C(x) · M^⟨-1⟩(x) = x`, i.e. `C(x) = x / M^⟨-1⟩(x)`. -/
theorem Cgf_mul_Minv : Cgf * Minv = X := by
  have h := sub_const_eq_X_mul_shift Minv
  rw [constantCoeff_Minv, map_zero, sub_zero] at h
  rw [h, mul_comm, mul_assoc, Cgf, mul_invOfUnit, mul_one]
  simp [coeff_one_Minv, ← coeff_zero_eq_constantCoeff_apply]

/-- The free cumulant `c_n = [x^n] C(x)`, a polynomial in the free moments. -/
noncomputable def freeCumulant (n : ℕ) : MvPolynomial ℕ ℤ := coeff n Cgf

/-! ### The moment–cumulant relation `C(M(x)) = M(x)/x` -/

/-- `P(x) = 1 + m₁ x + m₂ x² + ⋯ = M(x)/x`. -/
noncomputable def P : PowerSeries (MvPolynomial ℕ ℤ) := PowerSeries.mk mom

theorem M_eq : M = X * P := by
  ext n; cases n <;> simp [M, P, coeff_succ_X_mul]

theorem hasSubst_M : HasSubst M := HasSubst.of_constantCoeff_zero' constantCoeff_M

theorem Cgf_subst_M : (Cgf.subst M : PowerSeries (MvPolynomial ℕ ℤ)) = P := by
  have h1 : ((Cgf * Minv).subst M : PowerSeries (MvPolynomial ℕ ℤ)) =
      (Cgf.subst M : PowerSeries (MvPolynomial ℕ ℤ)) * X := by
    rw [subst_mul hasSubst_M, Minv_subst_M]
  rw [Cgf_mul_Minv, subst_X hasSubst_M] at h1
  refine PowerSeries.ext fun n => ?_
  have h2 := congrArg (coeff (n + 1)) h1
  have h3 := congrArg (coeff (n + 1)) M_eq
  rw [coeff_succ_mul_X] at h2
  rw [coeff_succ_X_mul] at h3
  rw [← h2, h3]

theorem coeff_M_pow (d e : ℕ) :
    coeff e (M ^ d) = if d ≤ e then coeff (e - d) (P ^ d) else 0 := by
  rw [M_eq, mul_pow, coeff_X_pow_mul']

theorem constantCoeff_P : constantCoeff P = 1 := by
  simp [P, mom, ← coeff_zero_eq_constantCoeff_apply]

theorem coeff_zero_P_pow (d : ℕ) : coeff 0 (P ^ d) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_P, one_pow]

/-- `∑_{d=0}^{e} c_d [x^(e-d)] P(x)^d = m_e`, the coefficient form of `C(M(x)) = P(x)`. -/
theorem cumulant_moment (e : ℕ) :
    ∑ d ∈ Finset.range (e + 1), freeCumulant d * coeff (e - d) (P ^ d) = mom e := by
  have h := congrArg (coeff e) Cgf_subst_M
  rw [coeff_subst' hasSubst_M, finsum_eq_sum_of_support_subset _ (s := Finset.range (e + 1))]
    at h
  · rw [P, coeff_mk] at h
    rw [← h]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_range] at hd
    rw [smul_eq_mul, coeff_M_pow, if_pos (by omega), freeCumulant, P]
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    rw [coeff_M_pow, if_neg (by omega), smul_zero]

theorem freeCumulant_zero : freeCumulant 0 = 1 := by
  simpa [mom, coeff_zero_P_pow] using cumulant_moment 0

theorem freeCumulant_succ (t : ℕ) : freeCumulant (t + 1) = mom (t + 1) -
    ∑ n ∈ Finset.range t, freeCumulant (n + 1) * coeff (t - n) (P ^ (n + 1)) := by
  have h := cumulant_moment (t + 1)
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at h
  simp only [Nat.sub_self, coeff_zero_P_pow, mul_one, pow_zero, Nat.sub_zero, coeff_one,
    Nat.add_one_ne_zero, if_false, mul_zero, add_zero, Nat.add_sub_add_right] at h
  rw [← h]
  ring

/-! ### Computable polynomial arithmetic -/

/-- A polynomial with integer coefficients in the moments `m_1, m_2, …`, as a list of terms
`(l, c)` standing for `c · m_{l₁} m_{l₂} ⋯` (repeated monomials are allowed: their coefficients
add up). Its meaning is `ev`. -/
abbrev Poly := List (List ℕ × ℤ)

/-- The meaning of a single term `(l, c)`: `c · ∏_{i ∈ l} m_i`. -/
noncomputable def tm (t : List ℕ × ℤ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.C t.2 * (t.1.map MvPolynomial.X).prod

/-- The polynomial denoted by `p : Poly`. -/
noncomputable def ev (p : Poly) : MvPolynomial ℕ ℤ := (p.map tm).sum

/-- Insert an index into a weakly increasing list of indices (keeps monomials sorted, so that
equal monomials are recognised by `addTerm`). -/
def insertIdx (i : ℕ) : List ℕ → List ℕ
  | [] => [i]
  | j :: l => if i ≤ j then i :: j :: l else j :: insertIdx i l

/-- Add one term to a polynomial, merging it with a term having the same index list. -/
def addTerm (t : List ℕ × ℤ) : Poly → Poly
  | [] => [t]
  | s :: p => if s.1 = t.1 then (s.1, s.2 + t.2) :: p else s :: addTerm t p

/-- Sum of two polynomials. -/
def padd (p q : Poly) : Poly := q.foldl (fun acc t => addTerm t acc) p

/-- Negation. -/
def pneg (p : Poly) : Poly := p.map fun t => (t.1, -t.2)

/-- Product of two polynomials. -/
def pmul (p q : Poly) : Poly :=
  p.foldl (fun acc s => q.foldl (fun acc' t => addTerm (s.1.foldr insertIdx t.1, s.2 * t.2) acc')
    acc) []

/-- Sum of a list of polynomials. -/
def psum (l : List Poly) : Poly := l.foldl padd []

/-- The coefficient of the monomial `∏_{i ∈ μ} m_i` (the multiset of indices `μ`). -/
def coeffOf (p : Poly) (μ : List ℕ) : ℤ :=
  (p.map fun t => if (t.1 : Multiset ℕ) = μ then t.2 else 0).sum

@[simp] theorem ev_nil : ev [] = 0 := rfl

@[simp] theorem ev_cons (t : List ℕ × ℤ) (p : Poly) : ev (t :: p) = tm t + ev p := by
  simp [ev]

theorem ev_addTerm (t : List ℕ × ℤ) : ∀ p, ev (addTerm t p) = ev p + tm t
  | [] => by simp [addTerm]
  | s :: p => by
    unfold addTerm
    split_ifs with h
    · simp only [ev_cons, tm, h, map_add]
      ring
    · simp only [ev_cons, ev_addTerm t p]
      ring

theorem ev_foldl_addTerm : ∀ (q p : Poly),
    ev (q.foldl (fun acc t => addTerm t acc) p) = ev p + ev q
  | [], p => by simp
  | t :: q, p => by
    simp only [List.foldl_cons, ev_foldl_addTerm q, ev_addTerm, ev_cons]
    ring

@[simp] theorem ev_padd (p q : Poly) : ev (padd p q) = ev p + ev q := ev_foldl_addTerm q p

@[simp] theorem ev_pneg : ∀ p : Poly, ev (pneg p) = -ev p
  | [] => by simp [pneg]
  | t :: p => by
    have := ev_pneg p
    simp only [pneg, List.map_cons, ev_cons] at this ⊢
    rw [this, tm, tm, map_neg]
    ring

theorem prod_insertIdx (i : ℕ) : ∀ l : List ℕ,
    ((insertIdx i l).map MvPolynomial.X).prod =
      (MvPolynomial.X i : MvPolynomial ℕ ℤ) * (l.map MvPolynomial.X).prod
  | [] => by simp [insertIdx]
  | j :: l => by
    unfold insertIdx
    split_ifs
    · simp
    · simp only [List.map_cons, List.prod_cons, prod_insertIdx i l]
      ring

theorem prod_foldr_insertIdx (u v : List ℕ) :
    ((u.foldr insertIdx v).map MvPolynomial.X).prod =
      ((u.map MvPolynomial.X).prod : MvPolynomial ℕ ℤ) * (v.map MvPolynomial.X).prod := by
  induction u with
  | nil => simp
  | cons i u ih =>
    simp only [List.foldr_cons, prod_insertIdx, ih, List.map_cons, List.prod_cons]
    ring

theorem ev_inner (s : List ℕ × ℤ) : ∀ (q acc : Poly),
    ev (q.foldl (fun acc' t => addTerm (s.1.foldr insertIdx t.1, s.2 * t.2) acc') acc) =
      ev acc + tm s * ev q
  | [], acc => by simp
  | t :: q, acc => by
    simp only [List.foldl_cons, ev_inner s q, ev_addTerm, ev_cons, tm, prod_foldr_insertIdx,
      map_mul]
    ring

theorem ev_outer (q : Poly) : ∀ (p acc : Poly),
    ev (p.foldl (fun acc s => q.foldl
      (fun acc' t => addTerm (s.1.foldr insertIdx t.1, s.2 * t.2) acc') acc) acc) =
      ev acc + ev p * ev q
  | [], acc => by simp
  | s :: p, acc => by
    simp only [List.foldl_cons, ev_outer q p, ev_inner, ev_cons]
    ring

@[simp] theorem ev_pmul (p q : Poly) : ev (pmul p q) = ev p * ev q := by
  simp [pmul, ev_outer]

theorem ev_foldl_padd : ∀ (l : List Poly) (acc : Poly),
    ev (l.foldl padd acc) = ev acc + (l.map ev).sum
  | [], acc => by simp
  | p :: l, acc => by
    simp only [List.foldl_cons, ev_foldl_padd l, ev_padd, List.map_cons, List.sum_cons]
    ring

@[simp] theorem ev_psum (l : List Poly) : ev (psum l) = (l.map ev).sum := by
  simp [psum, ev_foldl_padd]

theorem sum_map_range {β : Type*} [AddCommMonoid β] (f : ℕ → β) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem prod_map_X (l : List ℕ) : (l.map MvPolynomial.X).prod =
    (MvPolynomial.monomial (Multiset.toFinsupp (l : Multiset ℕ)) 1 : MvPolynomial ℕ ℤ) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, ih, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
      ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton]

/-- `coeffOf` computes coefficients. -/
theorem coeff_ev (p : Poly) (μ : List ℕ) :
    MvPolynomial.coeff (Multiset.toFinsupp (μ : Multiset ℕ)) (ev p) = coeffOf p μ := by
  induction p with
  | nil => simp [coeffOf]
  | cons t p ih =>
    have h : coeffOf (t :: p) μ = (if (t.1 : Multiset ℕ) = μ then t.2 else 0) + coeffOf p μ := by
      simp [coeffOf]
    rw [h, ev_cons, MvPolynomial.coeff_add, ih, tm, prod_map_X, MvPolynomial.C_mul_monomial,
      mul_one, MvPolynomial.coeff_monomial]
    by_cases ht : (t.1 : Multiset ℕ) = μ <;> simp [ht]

/-! ### Computing the free cumulants -/

/-- The coefficient of `x^s` in `P(x) = 1 + m₁ x + m₂ x² + ⋯`. -/
def Pl (s : ℕ) : Poly := if s = 0 then [([], 1)] else [([s], 1)]

theorem ev_Pl (s : ℕ) : ev (Pl s) = mom s := by
  unfold Pl mom; split_ifs <;> simp [tm]

/-- The product of two power series given by their lists of coefficients, truncated to the
coefficients of `x^0, …, x^D`. -/
def serMul (D : ℕ) (f g : List Poly) : List Poly :=
  (List.range (D + 1)).map fun t =>
    psum ((List.range (t + 1)).map fun i => pmul (f.getD i []) (g.getD (t - i) []))

theorem ev_serMul (D : ℕ) (f g : List Poly) {t : ℕ} (ht : t ≤ D) :
    ev ((serMul D f g).getD t []) =
      ∑ i ∈ Finset.range (t + 1), ev (f.getD i []) * ev (g.getD (t - i) []) := by
  rw [serMul, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp [sum_map_range, Function.comp_def]

/-- `[P^0, P^1, …, P^n]`, each truncated to the coefficients of `x^0, …, x^D`. -/
def powsL (D : ℕ) : ℕ → List (List Poly)
  | 0 => [(List.range (D + 1)).map fun s => if s = 0 then [([], 1)] else []]
  | n + 1 => powsL D n ++ [serMul D ((powsL D n).getD n []) ((List.range (D + 1)).map Pl)]

theorem powsL_spec (D : ℕ) : ∀ n, (powsL D n).length = n + 1 ∧
    ∀ j ≤ n, ∀ s ≤ D, ev (((powsL D n).getD j []).getD s []) = coeff s (P ^ j)
  | 0 => by
    refine ⟨rfl, fun j hj s hs => ?_⟩
    obtain rfl : j = 0 := by omega
    rw [powsL, List.getD_cons_zero, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    by_cases h : s = 0 <;> simp [h, tm, coeff_one]
  | n + 1 => by
    obtain ⟨hl, hs⟩ := powsL_spec D n
    refine ⟨by simp [powsL, hl], fun j hj s hsD => ?_⟩
    rw [powsL]
    rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact hs j (by omega) s hsD
    · obtain rfl : j = n + 1 := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_cons_zero,
        ev_serMul D _ _ hsD, pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i k => coeff i (P ^ n) * coeff k P)]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [hs n le_rfl i (by omega), List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by omega), Option.map_some, Option.getD_some, ev_Pl, P, coeff_mk]

/-- `[c_0, c_1, …, c_t]`, computed by the recursion `freeCumulant_succ`, given the table `pw` of
the coefficients of the powers of `P` (see `powsL`). -/
def cumsL (pw : List (List Poly)) : ℕ → List Poly
  | 0 => [[([], 1)]]
  | t + 1 => cumsL pw t ++ [padd (Pl (t + 1)) (pneg (psum ((List.range t).map fun n =>
      pmul ((cumsL pw t).getD (n + 1) []) ((pw.getD (n + 1) []).getD (t - n) []))))]

theorem cumsL_spec (D : ℕ) (pw : List (List Poly))
    (hpw : ∀ j ≤ D, ∀ s ≤ D, ev ((pw.getD j []).getD s []) = coeff s (P ^ j)) :
    ∀ t ≤ D, (cumsL pw t).length = t + 1 ∧
      ∀ j ≤ t, ev ((cumsL pw t).getD j []) = freeCumulant j
  | 0, _ => by
    refine ⟨rfl, fun j hj => ?_⟩
    obtain rfl : j = 0 := by omega
    simp [cumsL, tm, freeCumulant_zero]
  | t + 1, ht => by
    obtain ⟨hl, hc⟩ := cumsL_spec D pw hpw t (by omega)
    refine ⟨by simp [cumsL, hl], fun j hj => ?_⟩
    rw [cumsL]
    rcases Nat.lt_or_ge j (t + 1) with hjt | hjt
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact hc j (by omega)
    · obtain rfl : j = t + 1 := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_cons_zero,
        ev_padd, ev_pneg, ev_psum, ev_Pl, freeCumulant_succ, sub_eq_add_neg, List.map_map,
        sum_map_range]
      congr 2
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp only [Function.comp_apply, ev_pmul]
      rw [hc (i + 1) (by omega), hpw (i + 1) (by omega) (t - i) (by omega)]

/-- The `n`-th free cumulant, as a computed list of terms. -/
def cumPoly (n : ℕ) : Poly := (cumsL (powsL n n) n).getD n []

/-- `cumPoly n` is the free cumulant `c_n`. -/
theorem ev_cumPoly (n : ℕ) : ev (cumPoly n) = freeCumulant n :=
  (cumsL_spec n (powsL n n) (fun j hj s hs => (powsL_spec n n).2 j hj s hs) n le_rfl).2 n le_rfl

/-! ### Partitions in Abramowitz–Stegun order -/

/-- `partsAsc n j lo`: the partitions of `n` into exactly `j` parts, all of them `≥ lo`, each
written as a weakly increasing list, listed in increasing lexicographic order (the first part
`p` runs upward from `lo`, and the remaining parts form a partition of `n - p` into `j - 1`
parts `≥ p`). -/
def partsAsc (n : ℕ) : ℕ → ℕ → List (List ℕ)
  | 0, _ => if n = 0 then [[]] else []
  | j + 1, lo =>
    (List.range' lo (n + 1 - lo)).flatMap fun p => (partsAsc (n - p) j p).map (p :: ·)

/-- The partitions of `n` in Abramowitz–Stegun order (A036036): by increasing number of parts
`1, 2, …, n`, and for a fixed number of parts in increasing lexicographic order of the weakly
increasing lists of parts. -/
def asPartitions (n : ℕ) : List (List ℕ) :=
  (List.range n).flatMap fun j => partsAsc n (j + 1) 1

theorem mem_partsAsc : ∀ (j n lo : ℕ) (l : List ℕ), l ∈ partsAsc n j lo ↔
    l.length = j ∧ l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, lo ≤ x) ∧ l.sum = n
  | 0, n, lo, l => by
    unfold partsAsc
    split_ifs with h
    · subst h
      constructor
      · intro hl; simp at hl; simp [hl]
      · rintro ⟨h1, -, -, -⟩; simpa using h1
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro h1 _ _ h4
      rw [List.length_eq_zero_iff.1 h1] at h4
      exact h (h4.symm.trans rfl)
  | j + 1, n, lo, l => by
    simp only [partsAsc, List.mem_flatMap, List.mem_range'_1, List.mem_map]
    constructor
    · rintro ⟨x, hx, l', hl', rfl⟩
      obtain ⟨h1, h2, h3, h4⟩ := (mem_partsAsc j _ _ _).1 hl'
      refine ⟨by simp [h1], List.pairwise_cons.2 ⟨h3, h2⟩, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · omega
        · have := h3 y hy; omega
      · rw [List.sum_cons, h4]; omega
    · rintro ⟨h1, h2, h3, h4⟩
      cases l with
      | nil => simp at h1
      | cons x l' =>
        rw [List.pairwise_cons] at h2
        simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp,
          List.sum_cons] at h1 h3 h4
        refine ⟨x, ⟨h3.1, by omega⟩, l', (mem_partsAsc j _ _ _).2 ⟨h1, h2.2, h2.1, by omega⟩, rfl⟩

/-- `asPartitions n` lists exactly the partitions of `n`, written as nonempty weakly increasing
lists of positive integers with sum `n` (for `n = 0` the list is empty: row `0` is not part of
the triangle). -/
theorem mem_asPartitions (n : ℕ) (l : List ℕ) : l ∈ asPartitions n ↔
    l ≠ [] ∧ l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, 1 ≤ x) ∧ l.sum = n := by
  simp only [asPartitions, List.mem_flatMap, List.mem_range, mem_partsAsc]
  constructor
  · rintro ⟨j, -, h1, h2, h3, h4⟩
    exact ⟨fun h => by simp [h] at h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have := List.length_le_sum_of_one_le l h3
    have := List.length_pos_iff.2 h1
    exact ⟨l.length - 1, by omega, by omega, h2, h3, h4⟩

/-- `asPartitions n` lists each partition of `n` only once. -/
theorem nodup_asPartitions (n : ℕ) : (asPartitions n).Nodup := by
  have hp : ∀ j n lo, (partsAsc n j lo).Nodup := by
    intro j
    induction j with
    | zero => intro n lo; unfold partsAsc; split_ifs <;> simp
    | succ j ih =>
      intro n lo
      rw [partsAsc, List.nodup_flatMap]
      refine ⟨fun p _ => (ih _ _).map List.cons_injective, ?_⟩
      refine (List.nodup_range' (s := lo) (n := n + 1 - lo)).pairwise_of_forall_ne
        fun p _ q _ hpq => ?_
      rw [Function.onFun, List.disjoint_left]
      simp only [List.mem_map]
      rintro _ ⟨l, -, rfl⟩ ⟨l', -, h⟩
      exact hpq (List.cons_eq_cons.1 h).1.symm
  rw [asPartitions, List.nodup_flatMap]
  refine ⟨fun j _ => hp _ _ _, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun j _ j' _ hjj => ?_
  rw [Function.onFun, List.disjoint_left]
  intro l hl hl'
  rw [mem_partsAsc] at hl hl'
  exact hjj (by omega)

/-- The generator reproduces all 99 terms of A036036 listed in OEIS (rows `1, …, 6` and the
start of row `7`; kernel-checked). -/
theorem asPartitions_A036036 :
    ((List.range 7).flatMap fun n => (asPartitions (n + 1)).flatten).take 99 =
      [1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 1, 3,
        1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 2, 4, 3, 3, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1,
        1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 6, 2, 5, 3, 4, 1, 1, 5, 1, 2, 4,
        1, 3, 3, 2, 2, 3, 1, 1, 1] := by
  decide +kernel

/-! ### The sequence -/

/-- `T(n, k)`, for `n ≥ 1` and `0 ≤ k < p(n)`: the unsigned coefficient, in the free cumulant
`c_n`, of the monomial `m_{λ₁} m_{λ₂} ⋯` of the `k`-th partition `λ` of `n` in
Abramowitz–Stegun order (counting from `k = 0`). Computed from `cumPoly`; `T_eq_coeff` restates
it with `freeCumulant n`. -/
def T (n k : ℕ) : ℕ := (coeffOf (cumPoly n) ((asPartitions n).getD k [])).natAbs

/-- `T(n, k) = |[m_λ] c_n|` where `m_λ = ∏_{i ∈ λ} m_i` and `λ` is the `k`-th partition of `n` in
Abramowitz–Stegun order. -/
theorem T_eq_coeff (n k : ℕ) : T n k = (MvPolynomial.coeff
    (Multiset.toFinsupp ((asPartitions n).getD k [] : Multiset ℕ)) (freeCumulant n)).natAbs := by
  rw [T, ← ev_cumPoly, coeff_ev]

/-- A350499 (offset `1`): the irregular triangle `T` read by rows `n = 1, 2, 3, …`, row `n`
having `p(n)` entries (one per partition of `n`). Rows `1, …, i` contain at least `i` entries, so
entry number `i` of the concatenation lies among them. -/
def a (i : ℕ) : ℕ :=
  ((List.range i).flatMap fun n =>
    (List.range (asPartitions (n + 1)).length).map (T (n + 1))).getD (i - 1) 0

/-- The definition reproduces all 66 terms listed in OEIS, `a 1, …, a 66` (rows `1, …, 8`;
kernel-checked). -/
theorem a_data : (List.range 66).map (fun i => a (i + 1)) =
    [1, 1, 1, 1, 3, 2, 1, 4, 2, 10, 5, 1, 5, 5, 15, 15, 35, 14, 1, 6, 6, 3, 21, 42, 7, 56, 84,
      126, 42, 1, 7, 7, 7, 28, 56, 28, 28, 84, 252, 84, 210, 420, 462, 132, 1, 8, 8, 8, 4, 36,
      72, 72, 36, 36, 120, 360, 180, 360, 30, 330, 1320, 660, 792, 1980, 1716, 429] := by
  decide +kernel

/-- Sanity check of the signs (kernel-checked): the signed coefficients of `c_1, …, c_5` in
Abramowitz–Stegun order, as in the entry's EXAMPLE section: `c_1 = m_1`, `c_2 = m_2 - m_1^2`,
`c_3 = m_3 - 3 m_2 m_1 + 2 m_1^3`, `c_4 = m_4 - 4 m_3 m_1 - 2 m_2^2 + 10 m_2 m_1^2 - 5 m_1^4`,
`c_5 = m_5 - 5 m_4 m_1 - 5 m_2 m_3 + 15 m_3 m_1^2 + 15 m_2^2 m_1 - 35 m_2 m_1^3 + 14 m_1^5`
(by `coeff_ev` and `ev_cumPoly` these are the coefficients of `freeCumulant n`). -/
theorem cumulant_examples :
    (List.range 5).map (fun n => (asPartitions (n + 1)).map (coeffOf (cumPoly (n + 1)))) =
      [[1], [1, -1], [1, -3, 2], [1, -4, -2, 10, -5], [1, -5, -5, 15, 15, -35, 14]] := by
  decide +kernel

/-! ### Kurkov's recursion and the conjecture -/

/-- Kurkov's array over a commutative ring `A` with moments `m : ℕ → A`:
`R(1, k) = m_k` and `R(n, k) = R(n-1, k+1) - ∑_{j=1}^{n-1} R(j, k) R(n-j, 1)` for `n > 1`
(see `R_one`, `R_rec`). (`R(0, k) = 0` is a junk value; it is never used by the recursion for
`n ≥ 1`. Likewise only `m_k` with `k ≥ 1` enter `R(n, k)` for `n, k ≥ 1`.) In the sum below,
`j : Fin (n + 1)` stands for the index `j + 1 ∈ {1, …, n + 1}`. -/
def R {A : Type*} [CommRing A] (m : ℕ → A) : ℕ → ℕ → A
  | 0, _ => 0
  | 1, k => m k
  | n + 2, k => R m (n + 1) (k + 1) - ∑ j : Fin (n + 1), R m (j + 1) k * R m (n + 1 - j) 1
termination_by n => n
decreasing_by all_goals omega

theorem R_one {A : Type*} [CommRing A] (m : ℕ → A) (k : ℕ) : R m 1 k = m k := by
  rw [R]

/-- Kurkov's recursion, literally: `R(n,k) = R(n-1,k+1) - ∑_{j=1}^{n-1} R(j,k) R(n-j,1)` for
`n > 1`. -/
theorem R_rec {A : Type*} [CommRing A] (m : ℕ → A) {n : ℕ} (hn : 1 < n) (k : ℕ) :
    R m n k = R m (n - 1) (k + 1) - ∑ j ∈ Finset.Icc 1 (n - 1), R m j k * R m (n - j) 1 := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rw [R, show n + 2 - 1 = n + 1 by omega,
    Fin.sum_univ_eq_sum_range (fun j => R m (j + 1) k * R m (n + 1 - j) 1)]
  congr 1
  rw [show Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 2) by ext; simp; omega,
    Finset.sum_Ico_eq_sum_range, show n + 2 - 1 = n + 1 by omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 1 + j = j + 1 by omega, show n + 2 - (j + 1) = n + 1 - j by omega]

/-- Conjecture (Mikhail Kurkov, 2025): the free cumulants in terms of the free moments are
`c_n = R(n, 1)` for `n > 0`, where `R` is Kurkov's array with `R(1, k) = m_k`; as an identity of
polynomials over `ℤ` in the indeterminate moments `m_k = X k`. -/
def statement : Prop :=
  ∀ n : ℕ, 0 < n → R (fun k => (MvPolynomial.X k : MvPolynomial ℕ ℤ)) n 1 = freeCumulant n

end Math0.Statements.A350499
