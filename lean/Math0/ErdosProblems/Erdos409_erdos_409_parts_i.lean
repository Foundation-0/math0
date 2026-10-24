/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«409»
import Math0.Audit

/-!
# Erdős Problem 409 (i): the constant-answer formulation is refuted

Erdős Problem 409 asks how many iterations of `n ↦ φ(n) + 1` are needed, starting from `n`,
before a prime is reached. The upstream statement `erdos_409.parts.i` uses one unknown
`erdos_409.parts.i.answer : ℕ` that does not depend on `n`, while quantifying over every `n > 0`.
We prove that no natural number works: for `n = 2` the least number of iterations is `0`
(since `2` is prime), while for `n = 4` it is not `0` (since `4` is not prime; in fact it is `1`,
as `φ(4) + 1 = 3`). This is a defect of the formalization (the intended answer is a function of
`n`, see the upstream `isTheta`/`isBigO`/`isLittleO` variants), not a resolution of the
mathematical problem.
-/

open scoped Nat

namespace Math0.Erdos409

/-- If the least number of iterations from `2` is `a`, then `a = 0`, because `2` is prime. -/
theorem eq_zero_of_isLeast_two {a : ℕ}
    (h : IsLeast { i | (φ · + 1)^[i] 2 |>.Prime } a) : a = 0 := by
  have h0 : (0 : ℕ) ∈ { i | (φ · + 1)^[i] 2 |>.Prime } := by
    simp only [Set.mem_ofPred_eq, Function.iterate_zero, id_eq]
    exact Nat.prime_two
  have := h.2 h0
  omega

/-- `0` is not the least number of iterations from `4`, because `4` is not prime. -/
theorem not_isLeast_four_zero : ¬ IsLeast { i | (φ · + 1)^[i] 4 |>.Prime } 0 := by
  intro h
  have h1 := h.1
  simp only [Set.mem_ofPred_eq, Function.iterate_zero, id_eq] at h1
  exact absurd h1 (by decide)

/-- No single natural number `a` is the least number of iterations of `n ↦ φ(n) + 1` needed to
reach a prime for every `n > 0`. -/
theorem erdos_409_parts_i_refuted : ∀ a : ℕ, ¬ ∀ (n : ℕ) (_ : 0 < n),
    IsLeast { i | (φ · + 1)^[i] n |>.Prime } a := by
  intro a h
  have h2 : a = 0 := eq_zero_of_isLeast_two (h 2 (by norm_num))
  subst h2
  exact not_isLeast_four_zero (h 4 (by norm_num))

end Math0.Erdos409

#math0_refutes_every_answer Math0.Erdos409.erdos_409_parts_i_refuted Erdos409.erdos_409.parts.i
  with Erdos409.erdos_409.parts.i.answer
