/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A229159
import Math0.Audit

/-!
# Every odd prime is a side of a Heronian triangle (A229159)

We prove Lagneau's conjecture: for every prime `p > 2` there is a non-degenerate integer-sided
triangle with integer area having a side of length `p`.

The idea: every odd `p = 2m + 1` is a leg of the Pythagorean triple
`(p, (p² - 1)/2, (p² + 1)/2) = (2m + 1, 2m² + 2m, 2m² + 2m + 1)`. This right triangle has area
`p (p² - 1)/4 = m (m + 1) (2m + 1)`, an integer. The triangle inequalities hold since the two
long sides differ by `1 < p`, and Heron's formula is a polynomial identity in `m`. Primality is
not needed: the argument works for every odd `p ≥ 3`.
-/

namespace Math0.Frontier.A229159
open Math0.Statements.A229159

/-- For every `m ≥ 1`, the right triangle `(2m + 1, 2m² + 2m, 2m² + 2m + 1)` is non-degenerate
and has integer area `m (m + 1) (2m + 1)`. -/
private theorem isIntTriangle_odd (m : ℕ) (hm : 1 ≤ m) :
    IsIntTriangle (2 * m + 1) (2 * m ^ 2 + 2 * m) (2 * m ^ 2 + 2 * m + 1)
      (m * (m + 1) * (2 * m + 1)) := by
  refine ⟨?_, by omega, ?_, ?_⟩
  · nlinarith
  · omega
  · push_cast
    ring

/-- Lagneau's conjecture (A229159) holds: every prime `p > 2` is a side of an integer-sided
triangle with integer area. -/
theorem result : statement := by
  intro p hp h2
  obtain ⟨m, rfl⟩ : Odd p := hp.odd_of_ne_two (by omega)
  exact ⟨_, _, _, _, isIntTriangle_odd m (by omega), Or.inl rfl⟩

end Math0.Frontier.A229159

#math0_settles Math0.Frontier.A229159.result Math0.Statements.A229159.statement
