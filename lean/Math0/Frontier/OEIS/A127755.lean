/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A127755
import Math0.Audit

/-!
# The inverse of the triangle `1/n! [k ≤ n ≤ 2k]` is an integer triangle

We prove Paul Barry's conjecture from OEIS A127755: every entry `T(n,k)` of the inverse of the
triangle `A(n,k) = 1/n!` (for `k ≤ n ≤ 2k`, `0` otherwise) is an integer.

The idea: the forward-substitution recursion already shows integrality, because
`n! · A(n,j) = [j ≤ n ≤ 2j]` is `0` or `1`. Hence
`T(n,k) = n! [n = k] - ∑_{j < n} [j ≤ n ≤ 2j] T(j,k)`,
and strong induction on `n` shows that every `T(n,k)` lies in the image of `ℤ → ℚ`.
(Equivalently `A = D⁻¹ B` with `D = diag(n!)` and `B` a `0/1` unitriangular matrix, so
`A⁻¹ = B⁻¹ D` is integral.)
-/

namespace Math0.Frontier.A127755
open Math0.Statements.A127755 Finset

/-- `n! · A(n,j)` is the `0/1` indicator of `j ≤ n ≤ 2j`. -/
private lemma factorial_mul_A (n j : ℕ) :
    (n.factorial : ℚ) * A n j = if j ≤ n ∧ n ≤ 2 * j then 1 else 0 := by
  have hc : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  unfold A
  split_ifs
  · field_simp
  · simp

/-- A `0/1` indicator is an integer. -/
private lemma ite_mem (p : Prop) [Decidable p] :
    (if p then (1 : ℚ) else 0) ∈ (Int.castRingHom ℚ).range := by
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

/-- Every entry `T(n,k)` (for all `k`) lies in the image of `ℤ` in `ℚ`, by strong induction
on `n` using the recursion `T_spec`. -/
private lemma T_mem (n : ℕ) : ∀ k : ℕ, T n k ∈ (Int.castRingHom ℚ).range := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k
  rw [T_spec]
  by_cases hk : k ≤ n
  · rw [if_pos hk, mul_sub, Finset.mul_sum]
    refine Subring.sub_mem _ (Subring.mul_mem _ ⟨n.factorial, by simp⟩ (ite_mem _))
      (Subring.sum_mem _ fun j hj => ?_)
    rw [← mul_assoc, factorial_mul_A]
    exact Subring.mul_mem _ (ite_mem _) (ih j (Finset.mem_range.mp hj) k)
  · rw [if_neg hk]
    exact Subring.zero_mem _

/-- OEIS A127755 (conjecture of Paul Barry): the inverse triangle has integer entries. -/
theorem result : statement := by
  intro n k _
  obtain ⟨z, hz⟩ := T_mem n k
  exact ⟨z, by simpa using hz.symm⟩

end Math0.Frontier.A127755

#math0_settles Math0.Frontier.A127755.result Math0.Statements.A127755.statement
