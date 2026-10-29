/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A083020
import Math0.Audit

/-!
# `3^(3^18) + 2` is divisible by `31^2` (A083020)

We refute Cino Hilliard's conjecture that every number `3^(3^n) + 2` is squarefree.

Counterexample: `n = 18`. Since `φ(31^2) = 930`, we have `3^930 ≡ 1 (mod 961)` (checked
directly). Write `3^18 = 387420489 = 930 · 416581 + 159`. Then
`3^(3^18) = (3^930)^416581 · 3^159 ≡ 3^159 ≡ 959 ≡ -2 (mod 961)`, so
`961 = 31 · 31` divides `3^(3^18) + 2`, and this number is not squarefree because `31` is not a
unit. (More generally `961 ∣ 3^(3^n) + 2` exactly when `n ≡ 18 (mod 60)`, so infinitely many of
these numbers fail to be squarefree; one counterexample suffices here.)
-/

namespace Math0.Frontier.A083020
open Math0.Statements.A083020

/-- `3^930 ≡ 1 (mod 961)`: the order of `3` modulo `31^2` divides `φ(31^2) = 930`. -/
private theorem pow_930 : 3 ^ 930 ≡ 1 [MOD 961] := by
  unfold Nat.ModEq
  decide +kernel

/-- `3^(3^18) = (3^930)^416581 · 3^159`, from `3^18 = 930 · 416581 + 159`. -/
private theorem split_exp : (3 : ℕ) ^ (3 ^ 18) = (3 ^ 930) ^ 416581 * 3 ^ 159 := by
  rw [← pow_mul, ← pow_add]
  norm_num

/-- `31 · 31` divides `3^(3^18) + 2`. -/
private theorem sq_dvd : 31 * 31 ∣ 3 ^ (3 ^ 18) + 2 := by
  have h : (3 ^ 930) ^ 416581 * 3 ^ 159 + 2 ≡ 1 ^ 416581 * 3 ^ 159 + 2 [MOD 961] :=
    ((pow_930.pow 416581).mul_right _).add_right _
  have h0 : 1 ^ 416581 * 3 ^ 159 + 2 ≡ 0 [MOD 961] := by
    unfold Nat.ModEq
    decide +kernel
  rw [split_exp]
  exact Nat.modEq_zero_iff_dvd.1 (h.trans h0)

/-- Hilliard's conjecture fails: `3^(3^18) + 2` is divisible by `31^2`, so it is not
squarefree. -/
theorem result : ¬ statement := by
  intro h
  have hu : IsUnit (31 : ℕ) := h 18 31 sq_dvd
  rw [Nat.isUnit_iff] at hu
  omega

end Math0.Frontier.A083020

#math0_settles Math0.Frontier.A083020.result Math0.Statements.A083020.statement
