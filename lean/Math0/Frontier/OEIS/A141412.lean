/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A141412
import Math0.Audit

/-!
# Denominators of Curtz's polynomials are Farhi's `d(n+1,k+1)`

We prove Marcus's conjecture on A141412: `T(n,k) = d(n+1,k+1)` for all `n, k`.

The idea is generating functions in `ℚ⟦X⟧`. Write `L = log(1+X) = ∑_{j ≥ 1} (-1)^(j+1) X^j/j`.
The recursion defining `c n k = [x^k] P(n,x)` says that the column series
`Cs k = ∑_n c(n,k) X^n` satisfy `X · Cs 0 = L` and `Cs (k+1) = L · Cs k`, so
`X · Cs k = L^(k+1)`. On the other side, the series
`F m = ∑_N (-1)^(N+m) |s(N,m)| m!/N! X^N` satisfy `(1+X) F(m+1)' = (m+1) F(m)` (this is
the Stirling recurrence `|s(N+1,m+1)| = N |s(N,m+1)| + |s(N,m)|`), `F 0 = 1`, and have zero
constant term for `m ≥ 1`; since `(1+X) L' = 1`, the powers `L^m` satisfy the same
differential recursion, so `F m = L^m` by uniqueness (`PowerSeries.derivative.ext`, after
cancelling the nonzero factor `1+X`). Comparing coefficients of `X^(n+1)` gives
`c n k = (-1)^(n+k) |s(n+1,k+1)| (k+1)!/(n+1)!`, and a sign does not change a denominator.
-/

namespace Math0.Frontier.A141412
open Math0.Statements.A141412 PowerSeries

/-- The power series `log(1+X) = ∑_{n ≥ 1} (-1)^(n+1) X^n / n`. -/
private noncomputable def L : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1 : ℚ) ^ (n + 1) / n

/-- The exponential generating function of the signed Stirling numbers of the first kind,
scaled by `m!`: `F m = ∑_N s(N,m) m!/N! X^N` with `s(N,m) = (-1)^(N+m) |s(N,m)|`. -/
private noncomputable def F (m : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun N =>
    (-1 : ℚ) ^ (N + m) * (Nat.stirlingFirst N m : ℚ) * (m.factorial : ℚ) / (N.factorial : ℚ)

/-- The column generating function `∑_n c(n,k) X^n`. -/
private noncomputable def Cs (k : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => c n k

/-- Coefficients of `(1+X) g'`. -/
private lemma coeff_one_add_X_mul_deriv (g : ℚ⟦X⟧) (N : ℕ) :
    coeff N ((1 + X) * d⁄dX ℚ g) = coeff (N + 1) g * (N + 1) + coeff N g * N := by
  cases N with
  | zero =>
    rw [add_mul, one_mul, map_add, coeff_zero_X_mul, coeff_derivative]
    simp
  | succ n =>
    rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    push_cast
    ring

/-- `(1+X) · log(1+X)' = 1`. -/
private lemma one_add_X_mul_deriv_L : (1 + X) * d⁄dX ℚ L = 1 := by
  ext N
  rw [coeff_one_add_X_mul_deriv, coeff_one]
  cases N with
  | zero => simp [L]
  | succ n =>
    simp only [L, coeff_mk, if_false, Nat.succ_ne_zero]
    push_cast
    field_simp
    ring

/-- The derivative identity `(1+X) F(m+1)' = (m+1) F(m)`, from the Stirling recurrence. -/
private lemma one_add_X_mul_deriv_F (m : ℕ) :
    (1 + X) * d⁄dX ℚ (F (m + 1)) = C ((m : ℚ) + 1) * F m := by
  ext N
  rw [coeff_one_add_X_mul_deriv, coeff_C_mul]
  simp only [F, coeff_mk]
  rw [Nat.stirlingFirst_succ_succ, Nat.factorial_succ N, Nat.factorial_succ m]
  have hN : (N.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `F m = log(1+X)^m`. -/
private lemma F_eq (m : ℕ) : F m = L ^ m := by
  induction m with
  | zero =>
    ext N
    cases N with
    | zero => simp [F]
    | succ n => simp [F]
  | succ m ih =>
    apply derivative.ext
    · have h1 : (1 + X : ℚ⟦X⟧) ≠ 0 := by
        intro h
        have := congrArg (constantCoeff (R := ℚ)) h
        simp at this
      apply mul_left_cancel₀ h1
      have key : (1 + X) * d⁄dX ℚ (L ^ (m + 1)) = C ((m : ℚ) + 1) * L ^ m := by
        rw [derivative_pow, Nat.add_sub_cancel]
        calc (1 + X) * (((m + 1 : ℕ) : ℚ⟦X⟧) * L ^ m * d⁄dX ℚ L)
            = ((m + 1 : ℕ) : ℚ⟦X⟧) * L ^ m * ((1 + X) * d⁄dX ℚ L) := by ring
          _ = C ((m : ℚ) + 1) * L ^ m := by
            rw [one_add_X_mul_deriv_L, mul_one, ← map_natCast (C (R := ℚ)), Nat.cast_succ]
      rw [one_add_X_mul_deriv_F, ih, key]
    · rw [map_pow]
      simp [F, L, ← coeff_zero_eq_constantCoeff_apply]

/-- `c n 0 = (-1)^n/(n+1)` for all `n`. -/
private lemma c_zero (n : ℕ) : c n 0 = (-1 : ℚ) ^ n / ((n : ℚ) + 1) := by
  cases n with
  | zero => simp [c]
  | succ n => simp [c]

/-- `Cs (k+1) = log(1+X) · Cs k`, i.e. the recursion of `c`. -/
private lemma Cs_succ (k : ℕ) : Cs (k + 1) = L * Cs k := by
  ext n
  rw [coeff_mul]
  cases n with
  | zero => simp [Cs, L, c]
  | succ n =>
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Cs, L, coeff_mk, c, if_true, zero_mul, zero_add, Nat.succ_ne_zero, if_false]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring

/-- `X · Cs k = log(1+X)^(k+1)`. -/
private lemma X_mul_Cs (k : ℕ) : X * Cs k = L ^ (k + 1) := by
  induction k with
  | zero =>
    ext n
    cases n with
    | zero => simp [L]
    | succ n =>
      rw [coeff_succ_X_mul, pow_one]
      simp only [Cs, L, coeff_mk, c_zero, Nat.succ_ne_zero, if_false]
      push_cast
      ring
  | succ k ih =>
    rw [Cs_succ, pow_succ, ← ih]
    ring

/-- Closed form: `c n k = s(n+1,k+1) (k+1)!/(n+1)!` with the signed Stirling number. -/
private lemma c_eq (n k : ℕ) :
    c n k = (-1 : ℚ) ^ (n + 1 + (k + 1)) * ((Nat.stirlingFirst (n + 1) (k + 1) : ℚ) *
      ((k + 1).factorial : ℚ) / ((n + 1).factorial : ℚ)) := by
  have h := congrArg (coeff (n + 1)) (X_mul_Cs k)
  rw [coeff_succ_X_mul, ← F_eq] at h
  simp only [Cs, F, coeff_mk] at h
  rw [h]
  ring

/-- Marcus's conjecture holds: `T(n,k) = d(n+1,k+1)` (in fact for all `n, k`). -/
theorem result : statement := by
  intro n k _
  rw [T, d, c_eq]
  rcases neg_one_pow_eq_or ℚ (n + 1 + (k + 1)) with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, Rat.neg_den]

end Math0.Frontier.A141412

#math0_settles Math0.Frontier.A141412.result Math0.Statements.A141412.statement
