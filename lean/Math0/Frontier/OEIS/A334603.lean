/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A334603
import Math0.Audit

/-!
# The period of `1/11^n` is `2 * 11^(n-1)`

We prove the FORMULA conjecture of OEIS A334603: for every `n ≥ 1`, the multiplicative order of
`10` modulo `11^n` (the period of the decimal expansion of `1/11^n`) is `2 * 11^(n-1)`.

Write `n = k + 1`. In `ZMod (11^(k+1))` we have `10^2 = 100 = 1 + 11 * 9` with `11 ∤ 9`, so by
Mathlib's `ZMod.orderOf_one_add_mul_prime` the element `10^2` has order exactly `11^k`. Hence
`10^(2 * 11^k) = 1`. The prime divisors of `2 * 11^k` are `2` and (for `k ≥ 1`) `11`:
* `10^(11^k) ≠ 1`, because reducing modulo `11` gives `(-1)^(11^k) = -1 ≠ 1`;
* `10^(2 * 11^(k-1)) = (10^2)^(11^(k-1)) ≠ 1`, since `0 < 11^(k-1) < 11^k = orderOf (10^2)`.
The order criterion `orderOf_eq_of_pow_and_pow_div_prime` then gives `orderOf 10 = 2 * 11^k`.
-/

namespace Math0.Frontier.A334603
open Math0.Statements.A334603

/-- In `ZMod (11 ^ (k + 1))`, the element `10 ^ 2 = 100 = 1 + 11 * 9` has order `11 ^ k`. -/
private theorem orderOf_hundred (k : ℕ) :
    orderOf ((10 : ZMod (11 ^ (k + 1))) ^ 2) = 11 ^ k := by
  have h := ZMod.orderOf_one_add_mul_prime (p := 11) (by norm_num) (by norm_num) 9
    (by decide) k
  have e : ((10 : ZMod (11 ^ (k + 1))) ^ 2) =
      1 + ((11 : ℕ) : ZMod (11 ^ (k + 1))) * ((9 : ℤ) : ZMod (11 ^ (k + 1))) := by
    push_cast
    norm_num
  rw [e]
  exact h

/-- An odd power of `10` is never `1` modulo `11 ^ (k + 1)`, since `10 ≡ -1 (mod 11)`. -/
private theorem ten_pow_odd_ne_one (k j : ℕ) (hj : Odd j) :
    (10 : ZMod (11 ^ (k + 1))) ^ j ≠ 1 := by
  intro h
  have h2 := congrArg (ZMod.castHom (dvd_pow_self 11 (Nat.succ_ne_zero k)) (ZMod 11)) h
  rw [map_pow, map_one, map_ofNat] at h2
  have h10 : (10 : ZMod 11) = -1 := by decide
  rw [h10, hj.neg_one_pow] at h2
  exact absurd h2 (by decide)

/-- The multiplicative order of `10` modulo `11 ^ (k + 1)` is `2 * 11 ^ k`. -/
private theorem orderOf_ten (k : ℕ) : orderOf (10 : ZMod (11 ^ (k + 1))) = 2 * 11 ^ k := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by positivity)
  · rw [pow_mul, ← orderOf_hundred k, pow_orderOf_eq_one]
  · intro q hq hqL
    rcases prime_dvd_two_mul_pow hq hqL with rfl | rfl
    · rw [Nat.mul_div_cancel_left _ (by norm_num)]
      exact ten_pow_odd_ne_one k _ (Odd.pow (by decide))
    · cases k with
      | zero => norm_num at hqL
      | succ k =>
        rw [show 2 * 11 ^ (k + 1) / 11 = 2 * 11 ^ k by rw [pow_succ]; omega, pow_mul]
        apply pow_ne_one_of_lt_orderOf (by positivity)
        rw [orderOf_hundred]
        exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)

/-- OEIS A334603 (FORMULA conjecture): for every `n ≥ 1`, the period of the decimal expansion of
`1/11^n` is `2 * 11^(n-1)`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, period_eq_orderOf (Nat.Coprime.pow_right _ (by norm_num)), orderOf_ten,
    Nat.add_sub_cancel]

end Math0.Frontier.A334603

#math0_settles Math0.Frontier.A334603.result Math0.Statements.A334603.statement
