/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A320099
import Math0.Audit

/-!
# Kagey's order-10 recurrence for no-leaf subgraphs of the `5 × n` grid holds

We prove Peter Kagey's conjecture (A320099): for every `n > 10`,
`a(n) = 103 a(n-1) + 1063 a(n-2) - 1873 a(n-3) - 20274 a(n-4) + 44071 a(n-5) - 10365 a(n-6)
- 20208 a(n-7) + 5959 a(n-8) + 2300 a(n-9) - 500 a(n-10)`.

**Idea.** The statement file proves `a n = (T ^ n) noH noH` for the `32 × 32` column transfer
matrix `T`, and that `fastRow k` is the row `noH` of `T ^ k`. Put `x P(x)` for the polynomial
`x^11 - 103 x^10 - 1063 x^9 + 1873 x^8 + 20274 x^7 - 44071 x^6 + 10365 x^5 + 20208 x^4
- 5959 x^3 - 2300 x^2 + 500 x`. The row vector `e_noH` is annihilated on the left by it:
`e_noH · (x P)(T) = 0`, i.e. the rows `fastRow 1, …, fastRow 11` satisfy one linear relation
(the left Krylov space of `e_noH` has dimension exactly `11`). This finite vector identity is
checked by the kernel on the explicit rows (`row_identity`, written without subtractions).
Multiplying it on the right by `T ^ m` and reading the entry at `noH` gives the recurrence for
`a (m + 11)`, for every `m` (`nat_identity`), with no induction needed.
-/

namespace Math0.Frontier.A320099
open Math0.Statements.A320099 Finset

/-- Mapping over `states` turns a pointwise sum into `zipWith (+)`. -/
private theorem map_add (f g : St → ℕ) :
    states.map (fun R => f R + g R) = List.zipWith (· + ·) (states.map f) (states.map g) := by
  rw [List.zipWith_map, List.zipWith_self]

/-- Mapping over `states` turns a pointwise scalar multiple into a mapped scalar multiple. -/
private theorem map_mul (c : ℕ) (f : St → ℕ) :
    states.map (fun R => c * f R) = (states.map f).map (c * ·) := by
  rw [List.map_map]; rfl

/-- The row `noH` of `T ^ k`, listed along `states`, is `fastRow k`. -/
private theorem map_row (k : ℕ) : states.map (fun R => (T ^ k) noH R) = fastRow k :=
  (fastRow_eq k).symm

/-- The left annihilation `e_noH · T P(T) = 0`, entry by entry (kernel-checked on the rows). -/
private theorem row_identity (R : St) :
    (T ^ 11) noH R + 1873 * (T ^ 8) noH R + 20274 * (T ^ 7) noH R + 10365 * (T ^ 5) noH R
      + 20208 * (T ^ 4) noH R + 500 * (T ^ 1) noH R =
    103 * (T ^ 10) noH R + 1063 * (T ^ 9) noH R + 44071 * (T ^ 6) noH R
      + 5959 * (T ^ 3) noH R + 2300 * (T ^ 2) noH R := by
  have h : states.map (fun R => (T ^ 11) noH R + 1873 * (T ^ 8) noH R + 20274 * (T ^ 7) noH R
      + 10365 * (T ^ 5) noH R + 20208 * (T ^ 4) noH R + 500 * (T ^ 1) noH R) =
      states.map (fun R => 103 * (T ^ 10) noH R + 1063 * (T ^ 9) noH R
      + 44071 * (T ^ 6) noH R + 5959 * (T ^ 3) noH R + 2300 * (T ^ 2) noH R) := by
    simp only [map_add, map_mul, map_row]
    decide +kernel
  exact (List.map_inj_left.1 h) R (mem_states R)

/-- The recurrence for the entries `(T ^ (k + m)) noH noH`, for every `m`. -/
private theorem nat_identity (m : ℕ) :
    (T ^ (11 + m)) noH noH + 1873 * (T ^ (8 + m)) noH noH + 20274 * (T ^ (7 + m)) noH noH
      + 10365 * (T ^ (5 + m)) noH noH + 20208 * (T ^ (4 + m)) noH noH
      + 500 * (T ^ (1 + m)) noH noH =
    103 * (T ^ (10 + m)) noH noH + 1063 * (T ^ (9 + m)) noH noH
      + 44071 * (T ^ (6 + m)) noH noH + 5959 * (T ^ (3 + m)) noH noH
      + 2300 * (T ^ (2 + m)) noH noH := by
  simp only [pow_add, Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun R _ => ?_
  have h := congrArg (· * (T ^ m) R noH) (row_identity R)
  simp only [add_mul, mul_assoc] at h
  exact h

/-- Kagey's recurrence holds for every `n > 10`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = 11 + m := ⟨n - 11, by omega⟩
  rw [show 11 + m - 1 = 10 + m by omega, show 11 + m - 2 = 9 + m by omega,
    show 11 + m - 3 = 8 + m by omega, show 11 + m - 4 = 7 + m by omega,
    show 11 + m - 5 = 6 + m by omega, show 11 + m - 6 = 5 + m by omega,
    show 11 + m - 7 = 4 + m by omega, show 11 + m - 8 = 3 + m by omega,
    show 11 + m - 9 = 2 + m by omega, show 11 + m - 10 = 1 + m by omega]
  simp only [a_eq_T]
  have h := nat_identity m
  zify at h
  linarith

end Math0.Frontier.A320099

#math0_settles Math0.Frontier.A320099.result Math0.Statements.A320099.statement
