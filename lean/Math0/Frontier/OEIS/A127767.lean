/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A127767
import Math0.Audit

/-!
# The inverse of the `1/C(n)` band triangle (A127767) has integer entries

We prove Paul Barry's conjecture that every entry `T(n,k)` of the inverse of the triangle
`A(n,k) = 1/C(n)` for `k ≤ n ≤ 2k` (and `0` otherwise) is an integer.

**Idea.** Write `A = D·M` with `D = diag(1/C(n))` and `M(n,k) = [k ≤ n ≤ 2k]`, a lower
unitriangular `0/1` matrix. Then `A⁻¹ = M⁻¹·D⁻¹`, so `T(n,k) = M⁻¹(n,k)·C(k)`, and `M⁻¹` is
integral since `M` is unitriangular over `ℤ`. Concretely, we prove by strong induction on `n`
that `T(n,k)` is an integer multiple of `C(k)`: by the forward-substitution recursion
`T(n,k) = C(n)·([n = k] - ∑_{j<n} A(n,j) T(j,k))`, and if `T(j,k) = z_j C(k)` for `j < n` then
`T(n,k) = C(k)·([n = k] - ∑_{j<n, j ≤ n ≤ 2j} z_j)`, using `C(n)·[n = k] = C(k)·[n = k]` and
`C(n)·A(n,j) = [j ≤ n ≤ 2j]`.
-/

namespace Math0.Frontier.A127767
open Math0.Statements.A127767
open Finset

/-- Every entry `T(n,k)` of the inverse triangle is an integer multiple of the Catalan
number `C(k)`. -/
private theorem T_eq_int_mul_cat (n : ℕ) : ∀ k : ℕ, ∃ z : ℤ, T n k = (z : ℚ) * (cat k : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k
  have h' : ∀ m, m < n → ∃ z : ℤ, T m k = (z : ℚ) * (cat k : ℚ) := fun m hm => ih m hm k
  choose! f hf using h'
  have hc : (cat n : ℚ) ≠ 0 := by exact_mod_cast (cat_pos n).ne'
  rw [T_spec]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    refine ⟨(if n = k then 1 else 0) -
      ∑ j ∈ range n, (if j ≤ n ∧ n ≤ 2 * j then f j else 0), ?_⟩
    have hs : ∑ j ∈ range n, A n j * T j k
        = (cat k : ℚ) / (cat n : ℚ) *
          ∑ j ∈ range n, ((if j ≤ n ∧ n ≤ 2 * j then f j else 0 : ℤ) : ℚ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hf j (Finset.mem_range.mp hj), A]
      split_ifs <;> push_cast <;> ring
    rw [hs]
    by_cases hnk : n = k
    · subst hnk
      push_cast
      field_simp
    · push_cast
      simp only [hnk, if_false]
      field_simp
      ring
  · exact ⟨0, by rw [if_neg hk]; simp⟩

/-- **A127767 conjecture.** Every entry `T(n,k)`, `0 ≤ k ≤ n`, of the inverse triangle is an
integer. -/
theorem result : statement := by
  intro n k _
  obtain ⟨z, hz⟩ := T_eq_int_mul_cat n k
  exact ⟨z * (cat k : ℤ), by rw [hz]; push_cast; ring⟩

end Math0.Frontier.A127767

#math0_settles Math0.Frontier.A127767.result Math0.Statements.A127767.statement
