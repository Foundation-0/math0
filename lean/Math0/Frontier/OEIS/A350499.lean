/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A350499
import Math0.Audit

/-!
# Kurkov's recursion computes the free cumulants (A350499)

We prove Mikhail Kurkov's conjecture: with `R(1, k) = m_k` and
`R(n, k) = R(n-1, k+1) - ∑_{j=1}^{n-1} R(j, k) R(n-j, 1)` for `n > 1`, one has `R(n, 1) = c_n`
(the `n`-th free cumulant) for every `n > 0`, as polynomials in the indeterminate moments.

**Idea.** Let `W = M^⟨-1⟩` and `C = x / W` (`Cgf`). For each `k` put
`T_k(x) = ∑_{j ≥ 0} m_{k+j} x^{j+1}` and `F_k = T_k ∘ W`. Then:

* `T_k = x (m_k + T_{k+1})`, so, substituting `W`, `F_k = W (m_k + F_{k+1})`; multiplying by `C`
  and using `C W = x` gives `F_k · C = x (m_k + F_{k+1})`.
* `T_1 = P - 1` and `P ∘ W = (C ∘ M) ∘ W = C ∘ (M ∘ W) = C`, so `F_1 = C - 1`.
* `F_k` has constant term `0` and `C` has constant term `1`.

Comparing coefficients of `x^n` (`n ≥ 1`) in `F_k · (1 + F_1) = x (m_k + F_{k+1})` gives exactly
`[x^1] F_k = m_k` and `[x^n] F_k = [x^{n-1}] F_{k+1} - ∑_{j=1}^{n-1} [x^j] F_k · [x^{n-j}] F_1`,
i.e. Kurkov's recursion. By strong induction on `n`, `R(n, k) = [x^n] F_k` for all `n ≥ 1` and all
`k`; in particular `R(n, 1) = [x^n] (C - 1) = c_n`.
-/

namespace Math0.Frontier.A350499
open Math0.Statements.A350499 PowerSeries

/-- The tail series `T_k(x) = ∑_{j ≥ 0} m_{k+j} x^{j+1}`. -/
private noncomputable def Tk (k : ℕ) : PowerSeries (MvPolynomial ℕ ℤ) :=
  PowerSeries.mk fun n => if n = 0 then 0 else MvPolynomial.X (k + n - 1)

/-- `T_k(x) = x (m_k + T_{k+1}(x))`. -/
private theorem Tk_eq (k : ℕ) :
    Tk k = X * (C (MvPolynomial.X k) + Tk (k + 1)) := by
  ext n
  rcases n with _ | n
  · simp [Tk]
  · rw [coeff_succ_X_mul]
    rcases n with _ | n <;> simp [Tk]

/-- `T_1(x) = P(x) - 1`. -/
private theorem Tk_one : Tk 1 = P - 1 := by
  ext n
  rcases n with _ | n
  · simp [Tk, P, mom]
  · simp [Tk, P, mom, coeff_one]

/-- `M^⟨-1⟩` can be substituted (its constant term is `0`). -/
private theorem hasSubst_Minv : HasSubst Minv :=
  HasSubst.of_constantCoeff_zero' constantCoeff_Minv

/-- `F_k = T_k(M^⟨-1⟩(x))`. -/
private noncomputable def F (k : ℕ) : PowerSeries (MvPolynomial ℕ ℤ) := (Tk k).subst Minv

/-- `F_k = M^⟨-1⟩ · (m_k + F_{k+1})`, by substituting `M^⟨-1⟩` into `Tk_eq`. -/
private theorem F_eq (k : ℕ) : F k = Minv * (C (MvPolynomial.X k) + F (k + 1)) := by
  rw [F, Tk_eq, subst_mul hasSubst_Minv, subst_X hasSubst_Minv, subst_add hasSubst_Minv,
    subst_C]
  rfl

/-- `P(M^⟨-1⟩(x)) = C(x)`, from `C(M(x)) = P(x)` and `M(M^⟨-1⟩(x)) = x`. -/
private theorem P_subst_Minv : P.subst Minv = Cgf := by
  rw [← Cgf_subst_M, subst_comp_subst_apply hasSubst_M hasSubst_Minv, M_subst_Minv, X_subst]

/-- `F_1 = C - 1`. -/
private theorem F_one : F 1 = Cgf - 1 := by
  rw [F, Tk_one, subst_sub hasSubst_Minv, P_subst_Minv, ← coe_substAlgHom hasSubst_Minv, map_one]

/-- Each `F_k` has constant term `0`. -/
private theorem constantCoeff_F (k : ℕ) : constantCoeff (F k) = 0 := by
  rw [F_eq, map_mul, constantCoeff_Minv, zero_mul]

/-- `C` has constant term `c_0 = 1`. -/
private theorem coeff_zero_Cgf : coeff 0 Cgf = 1 := freeCumulant_zero

/-- `F_k · C = x (m_k + F_{k+1})`. -/
private theorem F_mul_Cgf (k : ℕ) : F k * Cgf = X * (C (MvPolynomial.X k) + F (k + 1)) := by
  conv_lhs => rw [F_eq k]
  rw [mul_comm, ← mul_assoc, Cgf_mul_Minv]

/-- Coefficient of `x^(n+1)` in `F_mul_Cgf`:
`[x^(n+1)] F_k + ∑_{i<n} [x^(i+1)] F_k · [x^(n-i)] C = [x^n] (m_k + F_{k+1})`. -/
private theorem key (k n : ℕ) :
    coeff (n + 1) (F k) + ∑ i ∈ Finset.range n, coeff (i + 1) (F k) * coeff (n - i) Cgf =
      coeff n (C (MvPolynomial.X k) + F (k + 1)) := by
  have h := congrArg (coeff (n + 1)) (F_mul_Cgf k)
  rw [coeff_succ_X_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (F k) * coeff j Cgf), Finset.sum_range_succ', Finset.sum_range_succ]
    at h
  rw [← h, coeff_zero_eq_constantCoeff_apply (F k), constantCoeff_F, zero_mul, add_zero,
    Nat.sub_self, coeff_zero_Cgf, mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_sub_add_right]

/-- `R(n+1, k) = [x^(n+1)] F_k` for all `n` and `k` (strong induction on `n`). -/
private theorem R_eq_coeff (n : ℕ) : ∀ k,
    R (fun k => (MvPolynomial.X k : MvPolynomial ℕ ℤ)) (n + 1) k = coeff (n + 1) (F k) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    have hk := key k n
    rcases n with _ | n
    · simp at hk
      rw [R_one, hk, constantCoeff_F, add_zero]
    · rw [R, Fin.sum_univ_eq_sum_range
        (fun j => R (fun k => (MvPolynomial.X k : MvPolynomial ℕ ℤ)) (j + 1) k *
          R (fun k => (MvPolynomial.X k : MvPolynomial ℕ ℤ)) (n + 1 - j) 1) (n + 1),
        ih n (by omega) (k + 1)]
      have hs : ∀ j ∈ Finset.range (n + 1),
          R (fun k => (MvPolynomial.X k : MvPolynomial ℕ ℤ)) (j + 1) k *
            R (fun k => (MvPolynomial.X k : MvPolynomial ℕ ℤ)) (n + 1 - j) 1 =
          coeff (j + 1) (F k) * coeff (n + 1 - j) Cgf := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [ih j (by omega) k, show n + 1 - j = (n - j) + 1 by omega, ih (n - j) (by omega) 1,
          F_one, map_sub, coeff_one, if_neg (Nat.succ_ne_zero _), sub_zero]
      rw [Finset.sum_congr rfl hs]
      rw [map_add, coeff_C, if_neg (Nat.succ_ne_zero _), zero_add] at hk
      rw [← hk]
      ring

/-- Kurkov's conjecture holds: `R(n, 1) = c_n` for every `n > 0`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [R_eq_coeff, F_one, map_sub, coeff_one, if_neg (Nat.succ_ne_zero n), sub_zero]
  rfl

end Math0.Frontier.A350499

#math0_settles Math0.Frontier.A350499.result Math0.Statements.A350499.statement
