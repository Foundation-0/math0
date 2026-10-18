/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A393794
import Math0.Audit

/-!
# The 1089-trick map has two 9-digit fixed points

We refute the uniqueness conjecture of A393794. For `n = 5` the claimed unique 9-digit fixed
point is `a 5 = 109999890`, but `x = 108910890` also has 9 digits and is fixed by `T`:
`rev x = 98019801`, so `D = |x - rev x| = 10891089`, `rev D = 98019801`, and
`T x = 10891089 + 98019801 = 108910890 = x`. Since `x ≠ a 5`, uniqueness fails.
All of this is a small kernel computation.
-/

namespace Math0.Frontier.A393794
open Math0.Statements.A393794

/-- `108910890` has 9 digits, is fixed by `T`, and differs from `a 5` (kernel-checked). -/
private theorem witness :
    (Nat.digits 10 108910890).length = 5 + 4 ∧ T 108910890 = 108910890 ∧
      108910890 ≠ a 5 := by
  decide +kernel

/-- The conjecture fails at `n = 5`: `108910890` is a second 9-digit fixed point of `T`. -/
theorem result : ¬ statement := by
  intro h
  obtain ⟨hlen, hT, hne⟩ := witness
  exact hne ((h 5 (by norm_num)).2.2 108910890 hlen hT)

end Math0.Frontier.A393794

#math0_settles Math0.Frontier.A393794.result Math0.Statements.A393794.statement
