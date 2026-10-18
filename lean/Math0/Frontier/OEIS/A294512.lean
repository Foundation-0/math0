/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A294512
import Math0.Audit

/-!
# Lang's conjecture for A294512 fails at n = 164

The OEIS entry A294512 (denominators of `V n = ∑_{k=0}^{n} 1/((k+1)(3k+1))`) carries the
conjecture `a(n) = A250400(n+1)/(n+1)`, where `A250400(m)` is the numerator of the harmonic mean
of the first `m` octagonal numbers. We refute it with the explicit counterexample `n = 164`.

Since `∑_{j=1}^{n+1} 1/(j(3j-2)) = V n`, writing `V n = p/q` in lowest terms gives
`A250400(n+1) = (n+1) q / gcd(n+1, p)`, so the conjecture is equivalent to
`gcd(n+1, p) = 1`. At `n = 164` we have `11 ∣ 165` and `11 ∣ p`, and in fact
`A250400(165) * 11 = 165 * a(164)` exactly. This identity between two natural numbers of about
160 digits is checked by the kernel (`decide +kernel`). It shows `A250400(165)/165 = a(164)/11`,
which is not `a(164)` because `a(164)` is a positive denominator.
-/

namespace Math0.Frontier.A294512
open Math0.Statements.A294512

set_option maxHeartbeats 4000000 in
/-- The kernel-checked key identity `A250400(165) * 11 = 165 * a(164)`: the harmonic-mean
numerator at `m = 165` is only `165/11 = 15` times the denominator of `V 164`. -/
private theorem key : A250400 165 * 11 = 165 * a 164 := by
  decide +kernel

/-- Lang's conjecture `a(n) = A250400(n+1)/(n+1)` (A294512) is false: it fails at `n = 164`,
where `A250400(165)/165 = a(164)/11`. -/
theorem result : ¬ statement := by
  intro h
  have h1 := h 164
  have hk := key
  have hpos : 0 < a 164 := (V 164).den_pos
  have h2 : (A250400 165 : ℚ) = 165 * (a 164 : ℚ) := by
    rw [div_eq_iff (by norm_num)] at h1
    push_cast at h1 ⊢
    linarith
  have h3 : A250400 165 = 165 * a 164 := by exact_mod_cast h2
  omega

end Math0.Frontier.A294512

#math0_settles Math0.Frontier.A294512.result Math0.Statements.A294512.statement
