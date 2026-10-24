/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A071685
import Math0.Audit

/-!
# Reverse-divisor numbers are `1`, `12`, `78` or `89` mod `100`

We prove H. P. Dale's conjecture on A071685: if `n` is not a palindrome, `10 ∤ n`, and
`n ∣ R n` or `R n ∣ n` (`R` the decimal reversal), then `n mod 100 ∈ {1, 12, 78, 89}`.

**Idea.** Let `n ≥ 10` have `d` digits and put `P = 10^(d-2)`. Write
`rev2 x = 10 (x % 10) + x / 10` for the swap of the two digits of `x < 100`. Peeling off the
last two digits of `n` with `R_cons` gives `R n / P = rev2 (n % 100)`: the leading two digits
of `R n` are the last two digits of `n`, swapped. Applying this to `R n` (which has the same
length and `R (R n) = n`) gives `n / P = rev2 (R n % 100)`.

*Forward case* `R n = k n` (`k ≠ 1`). With `A = n / P ∈ [10, 99]` and `B = n % 100`:
`A = rev2 (k B mod 100)`, and comparing `k A P ≤ k n = R n < (rev2 B + 1) P` and
`rev2 B · P ≤ R n = k n < k (A + 1) P` gives `k A ≤ rev2 B < k (A + 1)`, so `k ≤ 9`.
A finite check over `k < 10`, `B < 100` (kernel `decide`) leaves only `(k, B) = (4, 78)` and
`(9, 89)`.

*Backward case* `n = k R n`. Then `m = R n` ends in a nonzero digit (else `10 ∣ n`),
`R m = n = k m` and `R m ≠ m`, so `(k, m % 100) ∈ {(4, 78), (9, 89)}` and
`n % 100 = k m % 100 ∈ {12, 1}`.
-/

namespace Math0.Frontier.A071685
open Math0.Statements.A071685

/-- Swap the two decimal digits of a number below `100`. -/
private def rev2 (x : ℕ) : ℕ := 10 * (x % 10) + x / 10

/-- For `n ≥ 10`, `n` has two more digits than `n / 100`. -/
private theorem len_two {n : ℕ} (hn : 10 ≤ n) :
    (Nat.digits 10 n).length = (Nat.digits 10 (n / 100)).length + 2 := by
  have h1 : 0 < n := by omega
  have h2 : 0 < n / 10 := by omega
  have h3 : n / 10 / 10 = n / 100 := by omega
  rw [len_cons h1, len_cons h2, h3]

/-- The leading two digits of `R n` are the last two digits of `n`, swapped. -/
private theorem R_div_P {n : ℕ} (hn : 10 ≤ n) :
    R n / 10 ^ (Nat.digits 10 (n / 100)).length = rev2 (n % 100) := by
  have h1 : 0 < n := by omega
  have h2 : 0 < n / 10 := by omega
  have h3 : n / 10 / 10 = n / 100 := by omega
  have e1 := R_cons h1
  have e2 := R_cons h2
  have e3 := len_cons h2
  rw [h3] at e2 e3
  have hlt := R_lt (n / 100)
  rw [e3, e2, pow_succ] at e1
  have hP0 : 0 < 10 ^ (Nat.digits 10 (n / 100)).length := by positivity
  generalize 10 ^ (Nat.digits 10 (n / 100)).length = P at e1 hlt hP0 ⊢
  generalize R (n / 100) = r at e1 hlt
  have e : R n = r + P * (10 * (n % 10) + n / 10 % 10) := by rw [e1]; ring
  rw [e, Nat.add_mul_div_left _ _ hP0, Nat.div_eq_of_lt hlt, zero_add]
  unfold rev2
  omega

/-- If `n ≥ 10` does not end in `0`, then `R n ≥ 10`. -/
private theorem R_ge {n : ℕ} (hn : 10 ≤ n) (h : n % 10 ≠ 0) : 10 ≤ R n := by
  by_contra hc
  have := (Nat.digits_length_le_iff (k := 1) (by norm_num : 1 < 10) (R n)).2 (by omega)
  rw [len_R h, len_two hn] at this
  omega

/-- The leading two digits of `n` are the last two digits of `R n`, swapped. -/
private theorem div_P {n : ℕ} (hn : 10 ≤ n) (h : n % 10 ≠ 0) :
    n / 10 ^ (Nat.digits 10 (n / 100)).length = rev2 (R n % 100) := by
  have hR := R_ge hn h
  have e := R_div_P hR
  rw [R_R h] at e
  have hl : (Nat.digits 10 (R n / 100)).length = (Nat.digits 10 (n / 100)).length := by
    have a := len_two hR
    have b := len_two hn
    rw [len_R h] at a
    omega
  rw [hl] at e
  exact e

/-- For `n ≥ 10`, `10 · 10^(d-2) ≤ n` where `d` is the number of digits of `n`. -/
private theorem P_le {n : ℕ} (hn : 10 ≤ n) :
    10 * 10 ^ (Nat.digits 10 (n / 100)).length ≤ n := by
  rcases Nat.eq_zero_or_pos (n / 100) with h0 | h0
  · rw [h0]
    simp
    omega
  · have := Nat.base_pow_length_digits_le 10 (n / 100) (by norm_num) h0.ne'
    omega

/-- The two-digit constraints on `(k, B)` in the forward case `R n = k n`, `B = n % 100`. -/
private def Ok (k B : ℕ) : Prop := B % 10 ≠ 0 ∧ k ≠ 1 ∧ 10 ≤ rev2 (B * k % 100) ∧
    k * rev2 (B * k % 100) ≤ rev2 B ∧ rev2 B < k * (rev2 (B * k % 100) + 1)

/-- `Ok` is decidable. -/
private instance : DecidableRel Ok := fun k B => by unfold Ok; infer_instance

/-- The finite check: the only solutions of the two-digit constraints are `(4, 78)`
and `(9, 89)`. -/
private theorem check :
    ∀ k < 10, ∀ B < 100, Ok k B → (k = 4 ∧ B = 78) ∨ (k = 9 ∧ B = 89) := by
  decide +kernel

/-- Forward case: if `R n = n k`, `n` is not a palindrome and does not end in `0`, then
`(k, n % 100)` is `(4, 78)` or `(9, 89)`. -/
private theorem fwd {n k : ℕ} (h10 : n % 10 ≠ 0) (hk : R n = n * k) (hpal : R n ≠ n) :
    (k = 4 ∧ n % 100 = 78) ∨ (k = 9 ∧ n % 100 = 89) := by
  have hn : 10 ≤ n := by
    by_contra hc
    apply hpal
    have h0 : 0 < n := by omega
    have e := R_cons h0
    rw [Nat.div_eq_of_lt (by omega : n < 10)] at e
    rw [e, Nat.mod_eq_of_lt (by omega : n < 10)]
    simp [R]
  have hA := div_P hn h10
  have hB := R_div_P hn
  have hRge := R_ge hn h10
  rw [hk] at hRge
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hRge)
  have hlo := P_le hn
  have hP0 : 0 < 10 ^ (Nat.digits 10 (n / 100)).length := by positivity
  generalize 10 ^ (Nat.digits 10 (n / 100)).length = P at hA hB hlo hP0
  rw [hk] at hA hB
  have hmod : n * k % 100 = n % 100 * k % 100 := (Nat.mod_mul_mod n k 100).symm
  rw [hmod] at hA
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hpal (by rw [hk, mul_one])
  have hAP : n / P * P ≤ n := Nat.div_mul_le_self n P
  have hnlt : n < (n / P + 1) * P := (Nat.div_lt_iff_lt_mul hP0).1 (Nat.lt_succ_self _)
  have hRP : n * k / P * P ≤ n * k := Nat.div_mul_le_self (n * k) P
  have hRlt : n * k < (n * k / P + 1) * P := (Nat.div_lt_iff_lt_mul hP0).1 (Nat.lt_succ_self _)
  have hA10 : 10 ≤ n / P := (Nat.le_div_iff_mul_le hP0).2 hlo
  rw [hA, hB] at *
  have hkA : k * rev2 (n % 100 * k % 100) ≤ rev2 (n % 100) := by
    have h1 : k * rev2 (n % 100 * k % 100) * P < (rev2 (n % 100) + 1) * P :=
      calc k * rev2 (n % 100 * k % 100) * P = k * (rev2 (n % 100 * k % 100) * P) := by ring
        _ ≤ k * n := Nat.mul_le_mul_left _ hAP
        _ = n * k := mul_comm _ _
        _ < _ := hRlt
    have := Nat.lt_of_mul_lt_mul_right h1
    omega
  have hBk : rev2 (n % 100) < k * (rev2 (n % 100 * k % 100) + 1) := by
    have h1 : rev2 (n % 100) * P < k * (rev2 (n % 100 * k % 100) + 1) * P :=
      calc rev2 (n % 100) * P ≤ n * k := hRP
        _ = k * n := mul_comm _ _
        _ < k * ((rev2 (n % 100 * k % 100) + 1) * P) :=
            Nat.mul_lt_mul_of_pos_left hnlt (by omega)
        _ = _ := by ring
    exact Nat.lt_of_mul_lt_mul_right h1
  have hk10 : k < 10 := by
    have : k * 10 ≤ k * rev2 (n % 100 * k % 100) := Nat.mul_le_mul_left _ hA10
    have : rev2 (n % 100) ≤ 99 := by unfold rev2; omega
    omega
  have hB100 : n % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have hB10 : n % 100 % 10 ≠ 0 := by omega
  rcases check k hk10 (n % 100) hB100 ⟨hB10, hk1, hA10, hkA, hBk⟩ with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-- Dale's conjecture on A071685: every term `n` satisfies `n mod 100 ∈ {1, 12, 78, 89}`. -/
theorem result : statement := by
  rintro n ⟨hpal, h10, hdiv⟩
  have hB0 : n % 10 ≠ 0 := fun e => h10 (Nat.dvd_of_mod_eq_zero e)
  rcases hdiv with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases fwd hB0 hk hpal with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  · have hm0 : R n % 10 ≠ 0 := by
      intro e
      apply h10
      rw [hk]
      exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero e) k
    have hRm : R (R n) = R n * k := by rw [R_R hB0]; exact hk
    have hpm : R (R n) ≠ R n := by rw [R_R hB0]; exact fun e => hpal e.symm
    rcases fwd hm0 hRm hpm with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

end Math0.Frontier.A071685

#math0_settles Math0.Frontier.A071685.result Math0.Statements.A071685.statement
