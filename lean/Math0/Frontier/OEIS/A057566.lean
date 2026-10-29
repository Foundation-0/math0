/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A057566
import Math0.Audit

/-!
# Layman's floor formula for A057566 fails at `n = 24`

The conjectured identity
`a(n) = 5*floor((2n^3 - 3n^2 - n)/24) + floor((2(n-1)^3 - 3(n-1)^2 - (n-1))/24) + n`
for the number `a(n)` of collinear triples in a `3 × n` grid is false for `n = 24`.
The grid `3 × 24` has `a 24 = 6360` collinear triples (the kernel evaluates the fast counter
`fastA 24`, which equals `a 24` by `a_eq_fastA`; this is also the listed OEIS term), while the
formula gives `5 * 1079 + 946 + 24 = 6365`. The floors are turned into integer division with
`statement_iff_ediv` and evaluated by `norm_num`.

(For comparison, the true count is `3 * C(n, 3) + ⌈n/2⌉^2 + ⌊n/2⌋^2`: triples inside one row,
plus triples with one point per row in columns `x, y, z` with `x + z = 2y`.)
-/

namespace Math0.Frontier.A057566
open Math0.Statements.A057566

/-- The `3 × 24` grid has exactly `6360` collinear triples (the kernel evaluates the fast
counter `fastA`, which equals `a` by `a_eq_fastA`). -/
private theorem a_24 : a 24 = 6360 := by
  rw [a_eq_fastA]
  decide +kernel

/-- Layman's formula is false: at `n = 24` it predicts `6365`, but `a 24 = 6360`. -/
theorem result : ¬ statement := by
  rw [statement_iff_ediv]
  intro h
  have h24 := h 24 (by norm_num)
  rw [a_24] at h24
  norm_num at h24

end Math0.Frontier.A057566

#math0_settles Math0.Frontier.A057566.result Math0.Statements.A057566.statement
