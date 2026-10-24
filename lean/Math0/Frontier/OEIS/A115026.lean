/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A115026
import Math0.Audit

/-!
# A115026 has a term greater than 370: `a 119 = 371`

The orbit of `119` under A101337 is `119 ↦ 1³ + 1³ + 9³ = 731 ↦ 7³ + 3³ + 1³ = 371`, and `371`
is a fixed point (`3³ + 7³ + 1³ = 371`, a narcissistic number). So the limit cycle of `119` is
`{371}` and `a 119 = 371 > 370`, refuting Dale's conjecture. The value `a 119 = 371` is checked
by the kernel, evaluating the frozen definition `a` directly (as `a_data` does for `a 1, …, a 65`).
-/

namespace Math0.Frontier.A115026
open Math0.Statements.A115026

/-- The 119th term of A115026 is `371` (kernel evaluation of `a`). -/
private theorem a_119 : a 119 = 371 := by
  decide +kernel

/-- Dale's conjecture fails: `a 119 = 371 > 370`. -/
theorem result : ¬ statement := by
  intro h
  have h119 := h 119 (by norm_num)
  rw [a_119] at h119
  omega

end Math0.Frontier.A115026

#math0_settles Math0.Frontier.A115026.result Math0.Statements.A115026.statement
