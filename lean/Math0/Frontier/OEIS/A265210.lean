/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A265210
import Math0.Audit

/-!
# Columns of the reversed ternary digits of `2^n`

We prove Conjecture 1 of OEIS A265210: column `k` of the triangle of reversed base-3 digits
of `2^n` has least period `p(k) = 2 * 3^(k-1)`, and for `k ≥ 2` each block of `p(k)`
consecutive entries contains each of the digits `0, 1, 2` exactly `2 * 3^(k-2)` times.

The entry of row `n` in column `k` is `⌊2^n / 3^(k-1)⌋ mod 3`, which only depends on
`2^n mod 3^k`. For `k = j + 2` write `B = 3^(j+1)`, `M = 3^(j+2) = 3B`, `r = 2 * 3^j`.
An induction (`x^3 = (3^(j+1) t - 1)^3`) gives `2^(3^j) = 3^(j+1) t - 1` with `t ≡ 1 (mod 3)`.
Consequently
* `2^B ≡ -1 (mod M)` and `2^(2B) ≡ 1 (mod M)`: the column has period `p = 2B`, and `B` is not
  a period (it maps the digit `0` of `2^(pB) ≡ 1` to the digit `2` of `-1`);
* `2^r ≡ 1 + B (mod M)`: shifting by `r` adds `2^n mod 3 ∈ {1, 2}` to the digit (mod 3), so
  `r` is not a period, and the three shifts `n, n + r, n + 2r` see each digit exactly once,
  which gives the equal frequencies in each window of length `3r = p`.
Any period `q < p` of the column would give the period `gcd q p`, a proper divisor of
`2 * 3^(j+1)`, hence a divisor of `B` or of `r`; both are excluded. Column `1` is
`1, 2, 1, 2, …` and is treated directly.
-/

namespace Math0.Frontier.A265210
open Math0.Statements.A265210

/-- The entry of row `n` in column `k` is the base-3 digit of `2^n` at the place `3^(k-1)`. -/
private lemma T_eq (n k : ℕ) : T n k = 2 ^ n / 3 ^ (k - 1) % 3 := by
  unfold T row
  exact Nat.getD_digits _ _ (by norm_num)

/-- Column `j + 2` in closed form. -/
private lemma T_eq' (n j : ℕ) : T n (j + 2) = 2 ^ n / 3 ^ (j + 1) % 3 := by
  rw [T_eq]
  rfl

/-- Row `n` has an entry in column `k ≥ 1` iff `3^(k-1) ≤ 2^n`. -/
private lemma len_iff (n k : ℕ) (hk : 1 ≤ k) : k ≤ (row n).length ↔ 3 ^ (k - 1) ≤ 2 ^ n := by
  unfold row
  constructor
  · intro h
    by_contra h'
    have := (Nat.digits_length_le_iff (b := 3) (k := k - 1) (by norm_num) (2 ^ n)).2 (not_le.1 h')
    omega
  · intro h
    by_contra h'
    have := (Nat.digits_length_le_iff (b := 3) (k := k - 1) (by norm_num) (2 ^ n)).1 (by omega)
    omega

/-- Lifting the exponent for `2 ≡ -1 (mod 3)`: `2^(3^j) = 3^(j+1) t - 1` with `t ≡ 1 (mod 3)`. -/
private lemma key (j : ℕ) : ∃ t : ℤ, (2 : ℤ) ^ (3 ^ j) = 3 ^ (j + 1) * t - 1 ∧ t % 3 = 1 := by
  induction j with
  | zero => exact ⟨1, by norm_num, by norm_num⟩
  | succ j ih =>
    obtain ⟨t, ht, ht3⟩ := ih
    refine ⟨3 * (3 ^ (2 * j) * t ^ 3 - 3 ^ j * t ^ 2) + t, ?_, ?_⟩
    · rw [pow_succ (3 : ℕ) j, pow_mul, ht]
      ring
    · generalize 3 ^ (2 * j) * t ^ 3 - 3 ^ j * t ^ 2 = X
      omega

/-- `2^(2 * 3^(j+1)) ≡ 1 (mod 3^(j+2))`. -/
private lemma E1 (j : ℕ) : 2 ^ (2 * 3 ^ (j + 1)) ≡ 1 [MOD 3 ^ (j + 2)] := by
  obtain ⟨t, ht, -⟩ := key (j + 1)
  rw [Nat.modEq_iff_dvd]
  push_cast
  rw [pow_mul', ht]
  exact ⟨2 * t - 3 ^ (j + 2) * t ^ 2, by ring⟩

/-- `2^(3^(j+1)) ≡ -1 (mod 3^(j+2))`. -/
private lemma E2 (j : ℕ) : 2 ^ (3 ^ (j + 1)) ≡ 3 ^ (j + 2) - 1 [MOD 3 ^ (j + 2)] := by
  obtain ⟨t, ht, -⟩ := key (j + 1)
  rw [Nat.modEq_iff_dvd, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
  push_cast
  rw [ht]
  exact ⟨1 - t, by ring⟩

/-- `2^(2 * 3^j) ≡ 1 + 3^(j+1) (mod 3^(j+2))`. -/
private lemma E3 (j : ℕ) : 2 ^ (2 * 3 ^ j) ≡ 1 + 3 ^ (j + 1) [MOD 3 ^ (j + 2)] := by
  obtain ⟨t, ht, ht3⟩ := key j
  obtain ⟨s, rfl⟩ : ∃ s, t = 3 * s + 1 := ⟨t / 3, by omega⟩
  rw [Nat.modEq_iff_dvd]
  push_cast
  rw [pow_mul', ht]
  exact ⟨1 + 2 * s - 3 ^ j * (3 * s + 1) ^ 2, by ring⟩

/-- The digit at the place `3^(j+1)` only depends on the residue mod `3^(j+2)`. -/
private lemma dig_congr (j a b : ℕ) (h : a ≡ b [MOD 3 ^ (j + 2)]) :
    a / 3 ^ (j + 1) % 3 = b / 3 ^ (j + 1) % 3 := by
  have hM : 3 ^ (j + 2) = 3 ^ (j + 1) * 3 := pow_succ 3 (j + 1)
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← hM]
  rw [h]

/-- Column `j + 2` has period `2 * 3^(j+1)` (on all rows). -/
private lemma per (j n : ℕ) :
    2 ^ (n + 2 * 3 ^ (j + 1)) / 3 ^ (j + 1) % 3 = 2 ^ n / 3 ^ (j + 1) % 3 := by
  refine dig_congr j _ _ ?_
  rw [pow_add 2 n]
  calc 2 ^ n * 2 ^ (2 * 3 ^ (j + 1)) ≡ 2 ^ n * 1 [MOD 3 ^ (j + 2)] := Nat.ModEq.mul_left _ (E1 j)
    _ = 2 ^ n := mul_one _

/-- Shifting by `2 * 3^j` adds `2^n mod 3` to the digit of column `j + 2`. -/
private lemma shift (j n : ℕ) :
    2 ^ (n + 2 * 3 ^ j) / 3 ^ (j + 1) % 3 = (2 ^ n / 3 ^ (j + 1) % 3 + 2 ^ n % 3) % 3 := by
  have hM : 3 ^ (j + 2) = 3 * 3 ^ (j + 1) := by ring
  have h2 : 2 ^ n * 3 ^ (j + 1) ≡ 2 ^ n % 3 * 3 ^ (j + 1) [MOD 3 ^ (j + 2)] := by
    unfold Nat.ModEq
    rw [hM, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right, Nat.mod_mod]
  have h1 : 2 ^ (n + 2 * 3 ^ j) ≡ 2 ^ n + 2 ^ n % 3 * 3 ^ (j + 1) [MOD 3 ^ (j + 2)] := by
    rw [pow_add 2 n]
    calc 2 ^ n * 2 ^ (2 * 3 ^ j) ≡ 2 ^ n * (1 + 3 ^ (j + 1)) [MOD 3 ^ (j + 2)] :=
          Nat.ModEq.mul_left _ (E3 j)
      _ = 2 ^ n + 2 ^ n * 3 ^ (j + 1) := by ring
      _ ≡ 2 ^ n + 2 ^ n % 3 * 3 ^ (j + 1) [MOD 3 ^ (j + 2)] := Nat.ModEq.add_left _ h2
  rw [dig_congr j _ _ h1, Nat.add_mul_div_right _ _ (by positivity)]
  generalize 2 ^ n / 3 ^ (j + 1) = X
  omega

/-- `2^n mod 3` is `1` or `2`. -/
private lemma two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => left; rfl
  | succ n ih => rw [pow_succ]; omega

/-- Shifting by an even amount does not change `2^n mod 3`. -/
private lemma mod_three_shift (j n : ℕ) : 2 ^ (n + 2 * 3 ^ j) % 3 = 2 ^ n % 3 := by
  have h4 : 4 ^ 3 ^ j ≡ 1 [MOD 3] := by
    calc 4 ^ 3 ^ j ≡ 1 ^ 3 ^ j [MOD 3] := Nat.ModEq.pow _ (show 4 % 3 = 1 % 3 from rfl)
      _ = 1 := one_pow _
  have e : 2 ^ (n + 2 * 3 ^ j) = 2 ^ n * 4 ^ 3 ^ j := by rw [pow_add, pow_mul]; norm_num
  rw [e]
  have h := Nat.ModEq.mul_left (2 ^ n) h4
  rw [mul_one] at h
  exact h

/-- If `2^n ≡ 1 (mod 3^(j+2))`, then the digit of row `n` in column `j + 2` is `0`, while the
digit of row `n + 3^(j+1)` is `2`. -/
private lemma digit_flip (j n : ℕ) (h : 2 ^ n ≡ 1 [MOD 3 ^ (j + 2)]) :
    2 ^ n / 3 ^ (j + 1) % 3 = 0 ∧ 2 ^ (n + 3 ^ (j + 1)) / 3 ^ (j + 1) % 3 = 2 := by
  have hB : 3 ≤ 3 ^ (j + 1) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM : 3 ^ (j + 2) = 3 ^ (j + 1) * 3 := pow_succ 3 (j + 1)
  constructor
  · rw [dig_congr j _ _ h, Nat.div_eq_of_lt (by omega)]
  · have h' : 2 ^ (n + 3 ^ (j + 1)) ≡ 3 ^ (j + 2) - 1 [MOD 3 ^ (j + 2)] := by
      rw [pow_add 2 n]
      calc 2 ^ n * 2 ^ (3 ^ (j + 1)) ≡ 1 * (3 ^ (j + 2) - 1) [MOD 3 ^ (j + 2)] :=
            Nat.ModEq.mul h (E2 j)
        _ = 3 ^ (j + 2) - 1 := one_mul _
    rw [dig_congr j _ _ h', hM]
    generalize 3 ^ (j + 1) = B at hB ⊢
    rw [Nat.div_eq_of_lt_le (k := 2) (by omega) (by omega)]

/-- A proper divisor of `2 * 3^(j+1)` divides `3^(j+1)` or `2 * 3^j`. -/
private lemma proper_dvd (j g : ℕ) (h : g ∣ 2 * 3 ^ (j + 1)) (hlt : g < 2 * 3 ^ (j + 1)) :
    g ∣ 3 ^ (j + 1) ∨ g ∣ 2 * 3 ^ j := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.1 h
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hz
  rcases (Nat.dvd_prime Nat.prime_two).1 hy with rfl | rfl
  · left
    rw [one_mul]
    exact pow_dvd_pow 3 hb
  · right
    have : b < j + 1 := by
      by_contra hcon
      have := Nat.pow_le_pow_right (by norm_num : 0 < 3) (not_lt.1 hcon)
      omega
    exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow 3 (by omega))

/-- A window of length `3r` splits into three shifted windows of length `r`. -/
private lemma count_three (f : ℕ → ℕ) (m r : ℕ) (h : ∀ x, f x + f (x + r) + f (x + r + r) = 1) :
    ∑ x ∈ Finset.Ico m (m + (r + r + r)), f x = r := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.sum_range_add,
    Finset.sum_range_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (g := fun _ => 1)]
  · simp
  · intro x _
    rw [show m + (r + x) = m + x + r by ring, show m + (r + r + x) = m + x + r + r by ring]
    exact h (m + x)

/-- The conjecture holds for column `1`. -/
private lemma col_one :
    (IsColPeriod 1 (p 1) ∧ ∀ q : ℕ, 0 < q → q < p 1 → ¬ IsColPeriod 1 q) := by
  have hT : ∀ n, T n 1 = 2 ^ n % 3 := fun n => by rw [T_eq]; simp
  refine ⟨fun n _ => ?_, fun q hq0 hq => ?_⟩
  · rw [hT, hT, show p 1 = 2 by rfl, pow_add]
    omega
  · have hq1 : q = 1 := by
      have : p 1 = 2 := rfl
      omega
    subst hq1
    intro hper
    have h0 := hper 0 (by decide)
    rw [hT, hT] at h0
    norm_num at h0

/-- The digit of `2^n` at the place `3^(j+1)`, i.e. the entry of row `n` in column `j + 2`. -/
private def dig (j n : ℕ) : ℕ := 2 ^ n / 3 ^ (j + 1) % 3

/-- `x` is a period of column `j + 2` on the rows that have an entry in that column. -/
private def Per (j x : ℕ) : Prop := ∀ n, 3 ^ (j + 1) ≤ 2 ^ n → dig j (n + x) = dig j n

/-- Multiples of periods are periods. -/
private lemma Per_mul (j x : ℕ) (hx : Per j x) (t : ℕ) : Per j (x * t) := by
  induction t with
  | zero => intro n _; simp
  | succ t ih =>
    intro n hn
    have hn' : 3 ^ (j + 1) ≤ 2 ^ (n + x * t) :=
      le_trans hn (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [show n + x * (t + 1) = (n + x * t) + x by ring, hx _ hn', ih n hn]

/-- If `q` and `P` are periods (with `gcd q P < P`), then so is `gcd q P`. -/
private lemma Per_gcd (j q P : ℕ) (hq : Per j q) (hP : Per j P) (hlt : Nat.gcd q P < P) :
    Per j (Nat.gcd q P) := by
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_gcd (k := P) (n := q) hlt
  have hdm := Nat.div_add_mod (q * c) P
  intro n hn
  have hn' : 3 ^ (j + 1) ≤ 2 ^ (n + Nat.gcd q P) :=
    le_trans hn (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [← Per_mul j P hP (q * c / P) _ hn',
    show n + Nat.gcd q P + P * (q * c / P) = n + q * c by omega]
  exact Per_mul j q hq c n hn

/-- The conjecture holds for column `j + 2`. -/
private lemma col_ge_two (j : ℕ) :
    (IsColPeriod (j + 2) (p (j + 2)) ∧ ∀ q : ℕ, 0 < q → q < p (j + 2) →
        ¬ IsColPeriod (j + 2) q) ∧
      (∀ m : ℕ, ∀ d : ℕ, d < 3 →
        ((Finset.Ico m (m + p (j + 2))).filter (fun n => T n (j + 2) = d)).card = 2 * 3 ^ j) := by
  have hp : p (j + 2) = 2 * 3 ^ (j + 1) := rfl
  have hTd : ∀ n, T n (j + 2) = dig j n := fun n => T_eq' n j
  have hlen : ∀ n, j + 2 ≤ (row n).length ↔ 3 ^ (j + 1) ≤ 2 ^ n :=
    fun n => len_iff n (j + 2) (by omega)
  refine ⟨⟨fun n _ => ?_, fun q hq0 hq => ?_⟩, fun m d hd => ?_⟩
  · rw [hTd, hTd, hp]
    exact per j n
  · intro hper
    have hPq : Per j q := fun n hn => by
      have := hper n ((hlen n).2 hn)
      rwa [hTd, hTd] at this
    have hPp : Per j (2 * 3 ^ (j + 1)) := fun n _ => per j n
    have hgq : Nat.gcd q (2 * 3 ^ (j + 1)) ≤ q := Nat.le_of_dvd hq0 (Nat.gcd_dvd_left _ _)
    have hPg : Per j (Nat.gcd q (2 * 3 ^ (j + 1))) := Per_gcd j _ _ hPq hPp (by omega)
    rcases proper_dvd j (Nat.gcd q (2 * 3 ^ (j + 1))) (Nat.gcd_dvd_right _ _) (by omega)
      with hd | hd
    · -- `3^(j+1)` would be a period
      obtain ⟨t, ht⟩ := hd
      have hPB : Per j (3 ^ (j + 1)) := by rw [ht]; exact Per_mul j _ hPg t
      have h1 : 2 ^ (2 * 3 ^ (j + 1) * 3 ^ (j + 1)) ≡ 1 [MOD 3 ^ (j + 2)] := by
        rw [pow_mul]
        calc (2 ^ (2 * 3 ^ (j + 1))) ^ 3 ^ (j + 1) ≡ 1 ^ 3 ^ (j + 1) [MOD 3 ^ (j + 2)] :=
              Nat.ModEq.pow _ (E1 j)
          _ = 1 := one_pow _
      have hn : 3 ^ (j + 1) ≤ 2 ^ (2 * 3 ^ (j + 1) * 3 ^ (j + 1)) :=
        le_trans (Nat.lt_two_pow_self).le
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by positivity)))
      have := hPB _ hn
      obtain ⟨ha, hb⟩ := digit_flip j _ h1
      unfold dig at this
      omega
    · -- `2 * 3^j` would be a period
      obtain ⟨t, ht⟩ := hd
      have hPr : Per j (2 * 3 ^ j) := by rw [ht]; exact Per_mul j _ hPg t
      have hn : 3 ^ (j + 1) ≤ 2 ^ 3 ^ (j + 1) := (Nat.lt_two_pow_self).le
      have := hPr _ hn
      unfold dig at this
      rw [shift j] at this
      have h3 := two_pow_mod_three (3 ^ (j + 1))
      have h4 : 2 ^ 3 ^ (j + 1) / 3 ^ (j + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
      generalize 2 ^ 3 ^ (j + 1) / 3 ^ (j + 1) % 3 = a at this h4
      omega
  · have hp3 : p (j + 2) = 2 * 3 ^ j + 2 * 3 ^ j + 2 * 3 ^ j := by rw [hp]; ring
    rw [Finset.card_filter, hp3]
    apply count_three
    intro x
    rw [hTd, hTd, hTd]
    unfold dig
    have e1 := shift j x
    have e2 := shift j (x + 2 * 3 ^ j)
    have e3 := mod_three_shift j x
    have h3 := two_pow_mod_three x
    rw [e2, e1, e3]
    have h4 : 2 ^ x / 3 ^ (j + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    generalize 2 ^ x / 3 ^ (j + 1) % 3 = a at h4 ⊢
    generalize 2 ^ x % 3 = s at h3 ⊢
    split_ifs <;> omega

/-- Conjecture 1 of A265210 holds: column `k` has least period `2 * 3^(k-1)`, and for `k ≥ 2`
the digits `0, 1, 2` are equally frequent in every block of `2 * 3^(k-1)` consecutive entries. -/
theorem result : statement := by
  intro k hk
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    exact ⟨col_one, fun h => absurd h (by norm_num)⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    obtain ⟨h1, h2⟩ := col_ge_two j
    refine ⟨h1, fun _ m _ d e hd he => ?_⟩
    rw [h2 m d hd, h2 m e he]

end Math0.Frontier.A265210

#math0_settles Math0.Frontier.A265210.result Math0.Statements.A265210.statement
