/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A395454
import Math0.Audit

/-!
# Alexandersson's recurrence for the row polynomials of A395454 (rows counted from 1)

We prove the frozen statement: for the row polynomials `P_m(t) = ∑_k T(m,k) t^k` of A395454
(entry numbering, `P_0 = 1`), for every `m ≥ 2`,
`P_m = (m-1)(1+t)·P_{m-1} + (t - t^2)·P'_{m-1} + 2(m-1)t·P_{m-2}`,
which is Alexandersson's conjecture with the rows counted from `1`.

**Reversed Eulerian polynomials.** Put `R_j(t) = ∑_{i=0}^{j} E2(j,i) t^{j-i}`. Since
`E2(j,i) = 0` for `i > j`, the recurrence of `E2` gives
`R_{j+1} = (j + (j+1)t)·R_j + (t - t^2)·R_j'`.

**Binomial transform.** Because `T(n,k) = ∑_j (-1)^{n-j} C(n,j) E2(j, n-k)`, reindexing
`k = n - i` gives `P_n = S_n := ∑_{j=0}^{n} C(n,j) (-t)^{n-j} R_j`.

**Recurrence.** Using `(t - t^2)·((-t)^k)' = k(1-t)(-t)^k`, the recurrence of `R_j`, Pascal's
rule `S_{n+1} = ∑_j C(n,j)((-t)^{n-j} R_{j+1} + (-t)^{n-j+1} R_j)` and
`(n+1)·C(n,j) = (n+1-j)·C(n+1,j)`, every quantity becomes a sum over `j ≤ n+1` of multiples of
`C(n+1,j)(-t)^{n+1-j}R_j` and `C(n+1,j)(-t)^{n+1-j}R_{j+1}`, and the identity
`S_{n+2} = (n+1)(1+t)S_{n+1} + (t-t^2)S_{n+1}' + 2(n+1)t S_n` holds term by term.
-/

namespace Math0.Frontier.A395454
open Math0.Statements.A395454
open Polynomial

/-- `E2(j, i) = 0` whenever `i > j`. -/
private theorem E2_eq_zero : ∀ j i : ℕ, j < i → E2 j i = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | j + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | j + 1, k + 1, h => by
      rw [E2, E2_eq_zero j k (by omega), E2_eq_zero j (k+1) (by omega)]; ring

/-- The column-`0` case of the recurrence of `E2`. -/
private theorem E2_succ_zero (j : ℕ) : E2 (j + 1) 0 = E2 j 0 := by rw [E2]

/-- The recurrence of `E2` with simplified integer coefficients. -/
private theorem E2_succ_succ (j k : ℕ) : E2 (j + 1) (k + 1) =
    (2 * (j : ℤ) - k) * E2 j k + ((k : ℤ) + 2) * E2 j (k + 1) := by
  rw [E2]; ring

/-- The reversed second-order Eulerian polynomial `R_j(t) = ∑_{i ≤ j} E2(j,i) t^{j-i}`. -/
private noncomputable def R (j : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (j + 1), C (E2 j i) * X ^ (j - i)

/-- `(t - t^2)·(t^k)' = k·(t^k - t^{k+1})`. -/
private theorem XX_deriv_pow (k : ℕ) :
    (X - X ^ 2) * derivative (X ^ k : ℤ[X]) = (k : ℤ[X]) * (X ^ k - X ^ (k + 1)) := by
  cases k with
  | zero => simp
  | succ k =>
    rw [derivative_X_pow]
    simp only [Nat.add_sub_cancel, map_natCast]
    push_cast
    ring

/-- `(t - t^2)·((-t)^k)' = k·(1 - t)·(-t)^k`. -/
private theorem XX_deriv_negpow (k : ℕ) :
    (X - X ^ 2) * derivative ((-X) ^ k : ℤ[X]) = (k : ℤ[X]) * (1 - X) * (-X) ^ k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [derivative_pow]
    simp only [Nat.add_sub_cancel, map_natCast, derivative_neg, derivative_X]
    push_cast
    ring

/-- Termwise expansion of the right-hand side of the recurrence of `R`. -/
private theorem R_rhs (j : ℕ) :
    ((j : ℤ[X]) + ((j : ℤ[X]) + 1) * X) * R j + (X - X ^ 2) * derivative (R j) =
      ∑ i ∈ Finset.range (j + 1), (C (E2 j i) * ((2 * (j : ℤ[X]) - (i : ℤ[X])) * X ^ (j - i))
        + C (E2 j i) * (((i : ℤ[X]) + 1) * X ^ (j - i + 1))) := by
  rw [R, Finset.mul_sum, derivative_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [derivative_C_mul, mul_left_comm (X - X ^ 2 : ℤ[X]), XX_deriv_pow, Nat.cast_sub hij]
  ring

/-- `R_{j+1} = (j + (j+1)t)·R_j + (t - t^2)·R_j'`. -/
private theorem R_succ (j : ℕ) :
    R (j + 1) = ((j : ℤ[X]) + ((j : ℤ[X]) + 1) * X) * R j + (X - X ^ 2) * derivative (R j) := by
  rw [R_rhs, Finset.sum_add_distrib]
  have hL : R (j + 1) = ∑ i ∈ Finset.range (j + 1),
        C (E2 j i) * ((2 * (j : ℤ[X]) - (i : ℤ[X])) * X ^ (j - i))
      + (∑ i ∈ Finset.range (j + 1), C (E2 j (i + 1)) * (((i : ℤ[X]) + 2) * X ^ (j - i))
        + C (E2 j 0) * X ^ (j + 1)) := by
    rw [R, Finset.sum_range_succ' _ (j + 1), ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [E2_succ_succ, Nat.add_sub_add_right]
      simp only [map_add, map_mul, map_sub, map_natCast, map_ofNat]
      ring
  have h1 : ∑ i ∈ Finset.range (j + 1), C (E2 j (i + 1)) * (((i : ℤ[X]) + 2) * X ^ (j - i))
      + C (E2 j 0) * X ^ (j + 1)
      = ∑ i ∈ Finset.range (j + 1), C (E2 j i) * (((i : ℤ[X]) + 1) * X ^ (j - i + 1)) := by
    rw [Finset.sum_range_succ (fun i => C (E2 j (i + 1)) * (((i : ℤ[X]) + 2) * X ^ (j - i))) j,
      Finset.sum_range_succ' (fun i => C (E2 j i) * (((i : ℤ[X]) + 1) * X ^ (j - i + 1))) j,
      E2_eq_zero j (j + 1) (by omega)]
    simp only [map_zero, zero_mul, add_zero, Nat.cast_zero, zero_add, one_mul, Nat.sub_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i < j := Finset.mem_range.mp hi
    rw [show j - (i + 1) + 1 = j - i by omega]
    push_cast
    ring
  rw [hL, h1]

/-- The binomial transform `S_n = ∑_{j ≤ n} C(n,j)·(-t)^{n-j}·R_j`. -/
private noncomputable def S (n : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ[X]) * (-X) ^ (n - j) * R j

/-- Pascal's rule applied to `S_{n+1}`. -/
private theorem S_succ (n : ℕ) : S (n + 1) =
    ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ[X]) *
      ((-X) ^ (n - j) * R (j + 1) + (-X) ^ (n - j + 1) * R j) := by
  have hA : ∑ j ∈ Finset.range (n + 1),
        ((n + 1).choose (j + 1) : ℤ[X]) * (-X) ^ (n + 1 - (j + 1)) * R (j + 1)
      = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ[X]) * ((-X) ^ (n - j) * R (j + 1))
        + ∑ j ∈ Finset.range (n + 1), (n.choose (j + 1) : ℤ[X]) * ((-X) ^ (n - j) * R (j + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.choose_succ_succ, Nat.add_sub_add_right]
    push_cast
    ring
  have hB : ∑ j ∈ Finset.range (n + 1), (n.choose (j + 1) : ℤ[X]) * ((-X) ^ (n - j) * R (j + 1))
      + ((n + 1).choose 0 : ℤ[X]) * (-X) ^ (n + 1 - 0) * R 0
      = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ[X]) * ((-X) ^ (n - j + 1) * R j) := by
    rw [Finset.sum_range_succ (fun j => (n.choose (j + 1) : ℤ[X]) * ((-X) ^ (n - j) * R (j + 1))) n,
      Finset.sum_range_succ' (fun j => (n.choose j : ℤ[X]) * ((-X) ^ (n - j + 1) * R j)) n,
      Nat.choose_succ_self]
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right, Nat.sub_zero, mul_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    rw [show n - (j + 1) + 1 = n - j by omega]
  rw [S, Finset.sum_range_succ' _ (n + 1), hA, add_assoc, hB, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Termwise form of `(t - t^2)·S_n'`, using the recurrence of `R`. -/
private theorem S_deriv (n : ℕ) : (X - X ^ 2) * derivative (S n) =
    ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ[X]) *
      (((n - j : ℕ) : ℤ[X]) * (1 - X) * (-X) ^ (n - j) * R j
        + (-X) ^ (n - j) * (R (j + 1) - ((j : ℤ[X]) + ((j : ℤ[X]) + 1) * X) * R j)) := by
  rw [S, derivative_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := XX_deriv_negpow (n - j)
  have h' : (X - X ^ 2) * derivative (R j) =
      R (j + 1) - ((j : ℤ[X]) + ((j : ℤ[X]) + 1) * X) * R j := by
    rw [R_succ]; ring
  rw [derivative_mul, derivative_mul, derivative_natCast]
  linear_combination ((n.choose j : ℤ[X]) * R j) * h + ((n.choose j : ℤ[X]) * (-X) ^ (n - j)) * h'

/-- `(n+1)·(-t)·S_n` as a sum over `j ≤ n+1`, via `(n+1)·C(n,j) = (n+1-j)·C(n+1,j)`. -/
private theorem S_mul (n : ℕ) : ((n : ℤ[X]) + 1) * (-X) * S n =
    ∑ j ∈ Finset.range (n + 1 + 1), ((n + 1).choose j : ℤ[X]) *
      (((n + 1 - j : ℕ) : ℤ[X]) * (-X) ^ (n + 1 - j) * R j) := by
  rw [S, Finset.mul_sum, Finset.sum_range_succ _ (n + 1), Nat.sub_self]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hc : (n.choose j : ℤ[X]) * ((n : ℤ[X]) + 1) =
      ((n + 1).choose j : ℤ[X]) * ((n + 1 - j : ℕ) : ℤ[X]) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ[X]) (Nat.choose_mul_succ_eq n j)
  have hp : (-X : ℤ[X]) ^ (n + 1 - j) = (-X) ^ (n - j) * (-X) := by
    rw [← pow_succ]; congr 1; omega
  rw [hp]
  linear_combination (-X) ^ (n - j) * (-X) * R j * hc

/-- The recurrence `S_{n+2} = (n+1)(1+t)S_{n+1} + (t-t^2)S_{n+1}' + 2(n+1)t S_n`. -/
private theorem S_rec (n : ℕ) : S (n + 2) =
    ((n : ℤ[X]) + 1) * (1 + X) * S (n + 1) + (X - X ^ 2) * derivative (S (n + 1))
      + 2 * ((n : ℤ[X]) + 1) * X * S n := by
  have h3 : 2 * ((n : ℤ[X]) + 1) * X * S n = -2 * (((n : ℤ[X]) + 1) * (-X) * S n) := by ring
  rw [h3, S_mul, S_deriv, show n + 2 = n + 1 + 1 from rfl, S_succ (n + 1)]
  conv_rhs => rw [S]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.cast_sub hjn]
  push_cast
  ring

/-- One summand of `S_n`, expanded into monomials `t^{n-i}`, `i ≤ n`. -/
private theorem S_term (n j : ℕ) (hj : j ≤ n) :
    (n.choose j : ℤ[X]) * (-X) ^ (n - j) * R j =
      ∑ i ∈ Finset.range (n + 1), C ((-1) ^ (n - j) * (n.choose j : ℤ) * E2 j i) * X ^ (n - i) := by
  rw [R, Finset.mul_sum]
  have h : ∀ i ∈ Finset.range (j + 1),
      (n.choose j : ℤ[X]) * (-X) ^ (n - j) * (C (E2 j i) * X ^ (j - i)) =
        C ((-1) ^ (n - j) * (n.choose j : ℤ) * E2 j i) * X ^ (n - i) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show n - i = (n - j) + (j - i) by omega, pow_add, neg_pow]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [Finset.sum_congr rfl h]
  have hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_subset_range.mpr (by omega)
  apply Finset.sum_subset hsub
  intro i hi hi'
  have hji : j < i := by
    simp only [Finset.mem_range] at hi hi'
    omega
  rw [E2_eq_zero j i hji]
  simp

/-- The row polynomial `P_n` equals the binomial transform `S_n`. -/
private theorem P_eq_S (n : ℕ) : P n = S n := by
  have h : ∀ j ∈ Finset.range (n + 1), (n.choose j : ℤ[X]) * (-X) ^ (n - j) * R j =
      ∑ i ∈ Finset.range (n + 1), C ((-1) ^ (n - j) * (n.choose j : ℤ) * E2 j i) * X ^ (n - i) :=
    fun j hj => S_term n j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [S, Finset.sum_congr rfl h, Finset.sum_comm, P, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.add_sub_cancel, T, Nat.sub_sub_self hin, map_sum, Finset.sum_mul]

/-- Alexandersson's recurrence for A395454 holds with the rows counted from `1`: for `n ≥ 3`,
`P(n) = (n - 2t + nt - 2)·P(n-1) + (t - t^2)·P'(n-1) + t(2n-4)·P(n-2)`, `P(n) = P1 n`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have a1 : P1 (m + 3) = S (m + 2) := by
    rw [P1, P_eq_S, show m + 3 - 1 = m + 2 by omega]
  have a2 : P1 (m + 3 - 1) = S (m + 1) := by
    rw [P1, P_eq_S, show m + 3 - 1 - 1 = m + 1 by omega]
  have a3 : P1 (m + 3 - 2) = S m := by
    rw [P1, P_eq_S, show m + 3 - 2 - 1 = m by omega]
  rw [a1, a2, a3, S_rec m]
  push_cast
  ring

end Math0.Frontier.A395454

#math0_settles Math0.Frontier.A395454.result Math0.Statements.A395454.statement
