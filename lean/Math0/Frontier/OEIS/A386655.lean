/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A386655
import Math0.Audit

/-!
# A386655 modulo 6 is eventually periodic with pattern `[1, 0, 3, 0, 3, 2]`

We prove Paul D. Hanna's conjecture: for `n ≥ 6`,
`a(n) = ∑_{k ≤ n} C(n,k) 2^(k(k+1)) (2^k - (n-k))^(n-k-1)` (the `k = n` term being `2^(n²)`)
satisfies `a(n) mod 6 = [1, 0, 3, 0, 3, 2][(n - 6) mod 6]`.

**Modulo 2.** Every term with `k ≥ 1` contains the factor `2^(k(k+1))` (or `2^(n²)`), so
`a(n) ≡ (1 - n)^(n-1) ≡ n + 1 (mod 2)` for `n ≥ 2`.

**Modulo 3.** Put `m = n - k`. As `2 ≡ -1` and `k(k+1)` is even, the term with index `m ≥ 1` is
`C(n,m) (s - m)^(m-1)` with `s = (-1)^(n-m) = (-1)^n (-1)^m`, and the term `m = 0` is
`(-1)^n`. By Fermat (`x^3 = x` in `ZMod 3`), `(s - m)^(m-1)` depends only on `m mod 6` for
`m ≥ 2`; any function of `m mod 6` with values in `ZMod 3` can be written as
`α(m) + (-1)^m β(m)` with `α, β ∈ span{1, m, C(m,2)}`, and we find explicitly
* `n` even: `α = 1 + m + C(m,2)`, `β = m - C(m,2)` (valid for all `m ≥ 0`);
* `n` odd: `α = -m + C(m,2)`, `β = -1 - C(m,2)` (valid for all `m ≠ 1`; at `m = 1` the true
  value exceeds it by `1`, contributing a correction `C(n,1) = n`).
Then `∑_m C(n,m) C(m,j) x^m = C(n,j) x^j (1+x)^(n-j)` kills the `(-1)^m` part for `n ≥ 3`
and gives `a(n) ≡ 2^n + n 2^(n-1) + C(n,2) 2^(n-2)` (`n` even), resp.
`a(n) ≡ -n 2^(n-1) + C(n,2) 2^(n-2) + n` (`n` odd), modulo 3. Since `2^2 ≡ 1` and
`C(n,2) ≡ n - n²`, these depend only on `n mod 6` and equal `[1, 0, 0, 0, 0, 2][n mod 6]`.
Combining with the parity gives the claimed residues modulo 6.
-/

namespace Math0.Frontier.A386655
open Math0.Statements.A386655

/-- Fermat's little theorem in `ZMod 3`. -/
private lemma pow3 : ∀ x : ZMod 3, x ^ 3 = x := by decide

/-- In `ZMod 3`, a positive power only depends on the parity of the exponent. -/
private lemma pow_red (x : ZMod 3) : ∀ e : ℕ, x ^ (e + 1) = x ^ (e % 2 + 1)
  | 0 => rfl
  | 1 => rfl
  | e + 2 => by
    have h : x ^ (e + 2 + 1) = x ^ (e + 1) := by
      rw [show e + 2 + 1 = e + 3 by omega, pow_add, pow3, pow_succ]
    rw [h, pow_red x e, show (e + 2) % 2 = e % 2 by omega]

/-- `C(m,2) ≡ m - m² (mod 3)`. -/
private lemma choose2 : ∀ m : ℕ, ((m.choose 2 : ℕ) : ZMod 3) = (m : ZMod 3) - (m : ZMod 3) ^ 2
  | 0 => by simp
  | m + 1 => by
    have h3 : (3 : ZMod 3) = 0 := by decide
    rw [Nat.choose_succ_succ', Nat.cast_add, choose2 m, Nat.choose_one_right]
    push_cast
    linear_combination (m : ZMod 3) * h3

/-- The function `c0 + c1 m + c2 C(m,2)` with values in `ZMod 3`. -/
private def lin (c0 c1 c2 : ZMod 3) (m : ℕ) : ZMod 3 := c0 + c1 * m + c2 * (m.choose 2 : ZMod 3)

/-- The reduced term `((-1)^m - m)^(m-1)` (case `n` even) as `α(m) + (-1)^m β(m)`. -/
private lemma coreE (m : ℕ) (hm : 2 ≤ m) :
    ((-1 : ZMod 3) ^ m - m) ^ (m - 1) = lin 1 1 1 m + (-1) ^ m * lin 0 1 (-1) m := by
  rw [show m - 1 = (m - 2) + 1 by omega, pow_red _ (m - 2)]
  unfold lin
  rw [choose2, neg_one_pow_eq_pow_mod_two (R := ZMod 3) m, ← ZMod.natCast_mod m 3,
    show (m - 2) % 2 = m % 6 % 2 by omega, show m % 2 = m % 6 % 2 by omega,
    show m % 3 = m % 6 % 3 by omega]
  have h6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize m % 6 = r at h6 ⊢
  interval_cases r <;> decide

/-- The reduced term `(-(-1)^m - m)^(m-1)` (case `n` odd) as `α(m) + (-1)^m β(m)`. -/
private lemma coreO (m : ℕ) (hm : 2 ≤ m) :
    ((-1) * (-1 : ZMod 3) ^ m - m) ^ (m - 1) = lin 0 (-1) 1 m + (-1) ^ m * lin (-1) 0 (-1) m := by
  rw [show m - 1 = (m - 2) + 1 by omega, pow_red _ (m - 2)]
  unfold lin
  rw [choose2, neg_one_pow_eq_pow_mod_two (R := ZMod 3) m, ← ZMod.natCast_mod m 3,
    show (m - 2) % 2 = m % 6 % 2 by omega, show m % 2 = m % 6 % 2 by omega,
    show m % 3 = m % 6 % 3 by omega]
  have h6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize m % 6 = r at h6 ⊢
  interval_cases r <;> decide

/-- `∑_m C(j+p,m) C(m,j) x^m = C(j+p,j) x^j (x+1)^p`. -/
private lemma sum_choose_choose {R : Type*} [CommRing R] (j p : ℕ) (x : R) :
    ∑ m ∈ Finset.range (j + p + 1), ((j + p).choose m : R) * (m.choose j : R) * x ^ m =
      ((j + p).choose j : R) * x ^ j * (x + 1) ^ p := by
  rw [show j + p + 1 = j + (p + 1) by omega, Finset.sum_range_add]
  have h0 : ∑ m ∈ Finset.range j, ((j + p).choose m : R) * (m.choose j : R) * x ^ m = 0 :=
    Finset.sum_eq_zero fun m hm => by
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hm)]; simp
  rw [h0, zero_add, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Nat.choose_mul (n := j + p) (k := j + i) (s := j) (Nat.le_add_right j i)
  rw [show j + p - j = p by omega, show j + i - j = i by omega] at h
  rw [← Nat.cast_mul, h, Nat.cast_mul, one_pow, mul_one, pow_add]
  ring

/-- `∑_m C(n,m) C(m,j) x^m = C(n,j) x^j (x+1)^(n-j)` for `j ≤ n`. -/
private lemma sum_choose_choose' {R : Type*} [CommRing R] (n j : ℕ) (hj : j ≤ n) (x : R) :
    ∑ m ∈ Finset.range (n + 1), (n.choose m : R) * (m.choose j : R) * x ^ m =
      (n.choose j : R) * x ^ j * (x + 1) ^ (n - j) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [sum_choose_choose, Nat.add_sub_cancel_left]

/-- Binomial transform of `α(m) + (-1)^m β(m)` in `ZMod 3`; the `β` part vanishes for `n ≥ 3`. -/
private lemma sum_lin (n : ℕ) (hn : 3 ≤ n) (c0 c1 c2 d0 d1 d2 : ZMod 3) :
    ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ZMod 3) * (lin c0 c1 c2 m + (-1) ^ m * lin d0 d1 d2 m) =
      c0 * 2 ^ n + c1 * n * 2 ^ (n - 1) + c2 * n.choose 2 * 2 ^ (n - 2) := by
  have e : ∀ m : ℕ, (n.choose m : ZMod 3) * (lin c0 c1 c2 m + (-1) ^ m * lin d0 d1 d2 m) =
      c0 * ((n.choose m : ZMod 3) * (m.choose 0 : ZMod 3) * 1 ^ m) +
      c1 * ((n.choose m : ZMod 3) * (m.choose 1 : ZMod 3) * 1 ^ m) +
      c2 * ((n.choose m : ZMod 3) * (m.choose 2 : ZMod 3) * 1 ^ m) +
      (d0 * ((n.choose m : ZMod 3) * (m.choose 0 : ZMod 3) * (-1) ^ m) +
      d1 * ((n.choose m : ZMod 3) * (m.choose 1 : ZMod 3) * (-1) ^ m) +
      d2 * ((n.choose m : ZMod 3) * (m.choose 2 : ZMod 3) * (-1) ^ m)) := by
    intro m
    simp only [lin, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_pow]
    ring
  rw [Finset.sum_congr rfl fun m _ => e m]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_choose_choose' n 0 (by omega) (1 : ZMod 3), sum_choose_choose' n 1 (by omega) (1 : ZMod 3),
    sum_choose_choose' n 2 (by omega) (1 : ZMod 3), sum_choose_choose' n 0 (by omega) (-1 : ZMod 3),
    sum_choose_choose' n 1 (by omega) (-1 : ZMod 3), sum_choose_choose' n 2 (by omega) (-1 : ZMod 3)]
  simp only [neg_add_cancel, zero_pow (show n ≠ 0 by omega), zero_pow (show n - 1 ≠ 0 by omega),
    zero_pow (show n - 2 ≠ 0 by omega), Nat.choose_zero_right, Nat.choose_one_right,
    Nat.sub_zero, one_pow, one_add_one_eq_two]
  ring

/-- `2^(k(k+1)) ≡ 1 (mod 3)`. -/
private lemma two_pow_mul_succ (k : ℕ) : (2 : ZMod 3) ^ (k * (k + 1)) = 1 := by
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self k
  rw [ht, ← two_mul, pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow]

/-- `(-1)^(n-m) = (-1)^n (-1)^m` for `m ≤ n`. -/
private lemma neg_one_pow_sub' (n m : ℕ) (h : m ≤ n) :
    (-1 : ZMod 3) ^ (n - m) = (-1) ^ n * (-1) ^ m := by
  have e : (-1 : ZMod 3) ^ (n - m) * (-1) ^ m = (-1) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel h]
  rw [← e, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]

/-- The summand with `k = n - m`, `1 ≤ m ≤ n`, modulo 3. -/
private lemma term_cast (n m : ℕ) (h1 : 1 ≤ m) (h : m ≤ n) :
    ((term n (n - m) : ℤ) : ZMod 3) =
      (n.choose m : ZMod 3) * ((-1) ^ n * (-1) ^ m - m) ^ (m - 1) := by
  have hne : n - m ≠ n := by omega
  have hk : n - (n - m) = m := by omega
  simp only [term, if_neg hne, hk, binom_eq_choose, Nat.choose_symm h]
  push_cast
  rw [two_pow_mul_succ, show (2 : ZMod 3) = -1 by decide, neg_one_pow_sub' n m h, mul_one]

/-- The summand with `k = n` is `2^(n²) ≡ (-1)^n (mod 3)`. -/
private lemma term_cast_self (n : ℕ) : ((term n n : ℤ) : ZMod 3) = (-1) ^ n := by
  simp only [term]
  push_cast
  rw [show (2 : ZMod 3) = -1 by decide, pow_mul]
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, one_pow]
  · rw [ho.neg_one_pow, ho.neg_one_pow]

/-- Reindex the defining sum by `m = n - k`. -/
private lemma a_reflect (n : ℕ) :
    ((a n : ℤ) : ZMod 3) = ∑ m ∈ Finset.range (n + 1), ((term n (n - m) : ℤ) : ZMod 3) := by
  unfold a
  push_cast
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show n + 1 - 1 - m = n - m by omega]

/-- Closed form of `a(n)` modulo 3 for even `n ≥ 3`. -/
private lemma a_mod3_even (n : ℕ) (hn : 3 ≤ n) (he : Even n) :
    ((a n : ℤ) : ZMod 3) = 1 * 2 ^ n + 1 * n * 2 ^ (n - 1) + 1 * n.choose 2 * 2 ^ (n - 2) := by
  rw [← sum_lin n hn 1 1 1 0 1 (-1), a_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rcases Nat.lt_or_ge m 2 with h | h
  · interval_cases m
    · rw [Nat.sub_zero, term_cast_self, he.neg_one_pow]
      simp [lin]
    · rw [term_cast n 1 le_rfl hm', Nat.sub_self, pow_zero, mul_one]
      have : lin 1 1 1 1 + (-1) ^ 1 * lin 0 1 (-1) 1 = 1 := by decide
      rw [this, mul_one]
  · rw [term_cast n m (by omega) hm', he.neg_one_pow, one_mul, coreE m h]

/-- Closed form of `a(n)` modulo 3 for odd `n ≥ 3`. -/
private lemma a_mod3_odd (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) :
    ((a n : ℤ) : ZMod 3) =
      0 * 2 ^ n + (-1) * n * 2 ^ (n - 1) + 1 * n.choose 2 * 2 ^ (n - 2) + n := by
  rw [← sum_lin n hn 0 (-1) 1 (-1) 0 (-1), a_reflect]
  have h1 : (n : ZMod 3) = ∑ m ∈ Finset.range (n + 1), if m = 1 then (n : ZMod 3) else 0 := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rcases Nat.lt_or_ge m 2 with h | h
  · interval_cases m
    · rw [Nat.sub_zero, term_cast_self, ho.neg_one_pow]
      simp [lin]
    · rw [term_cast n 1 le_rfl hm', Nat.sub_self, pow_zero, mul_one, if_pos rfl,
        Nat.choose_one_right]
      have : lin 0 (-1) 1 1 + (-1) ^ 1 * lin (-1) 0 (-1) 1 = 0 := by decide
      rw [this, mul_zero, zero_add]
  · rw [term_cast n m (by omega) hm', ho.neg_one_pow, coreO m h, if_neg (by omega), add_zero]

/-- For `n ≥ 6`, `a(n) mod 3` is `[1, 0, 0, 0, 0, 2][n mod 6]`. -/
private lemma a_mod3 (n : ℕ) (hn : 6 ≤ n) :
    ((a n : ℤ) : ZMod 3) = ((([1, 0, 0, 0, 0, 2] : List ℤ).getD (n % 6) 0 : ℤ) : ZMod 3) := by
  have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have h6 : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rcases Nat.even_or_odd n with he | ho
  · have hp : n % 6 % 2 = 0 := by have := Nat.even_iff.mp he; omega
    rw [a_mod3_even n (by omega) he, choose2, pow_eq_pow_mod n h2, pow_eq_pow_mod (n - 1) h2,
      pow_eq_pow_mod (n - 2) h2, ← ZMod.natCast_mod n 3,
      show (n - 1) % 2 = (n % 6 + 1) % 2 by omega, show (n - 2) % 2 = n % 6 % 2 by omega,
      show n % 2 = n % 6 % 2 by omega, show n % 3 = n % 6 % 3 by omega]
    generalize n % 6 = r at h6 hp ⊢
    interval_cases r <;> first | decide | omega
  · have hp : n % 6 % 2 = 1 := by have := Nat.odd_iff.mp ho; omega
    rw [a_mod3_odd n (by omega) ho, choose2, pow_eq_pow_mod n h2, pow_eq_pow_mod (n - 1) h2,
      pow_eq_pow_mod (n - 2) h2, ← ZMod.natCast_mod n 3,
      show (n - 1) % 2 = (n % 6 + 1) % 2 by omega, show (n - 2) % 2 = n % 6 % 2 by omega,
      show n % 2 = n % 6 % 2 by omega, show n % 3 = n % 6 % 3 by omega]
    generalize n % 6 = r at h6 hp ⊢
    interval_cases r <;> first | decide | omega

/-- In `ZMod 2`, every positive power of `x` is `x`. -/
private lemma pow_zmod2 (x : ZMod 2) : ∀ e : ℕ, x ^ (e + 1) = x
  | 0 => pow_one x
  | e + 1 => by
    rw [pow_succ, pow_zmod2 x e]
    revert x
    decide

/-- For `n ≥ 2`, `a(n) ≡ n + 1 (mod 2)`: every term with `k ≥ 1` is even. -/
private lemma a_mod2 (n : ℕ) (hn : 2 ≤ n) :
    ((a n : ℤ) : ZMod 2) = (((n : ℤ) + 1 : ℤ) : ZMod 2) := by
  unfold a
  push_cast
  rw [Finset.sum_eq_single 0]
  · simp only [term, if_neg (show (0 : ℕ) ≠ n by omega), binom_eq_choose, Nat.choose_zero_right,
      Nat.sub_zero]
    push_cast
    rw [show n - 1 = (n - 2) + 1 by omega, pow_zmod2, sub_eq_add_neg, ZMod.neg_eq_self_mod_two,
      add_comm, one_mul]
  · intro k _ hk0
    unfold term
    split_ifs with h
    · push_cast
      rw [show (2 : ZMod 2) = 0 by decide, zero_pow (by positivity)]
    · push_cast
      rw [show (2 : ZMod 2) = 0 by decide, zero_pow (show k * (k + 1) ≠ 0 by positivity)]
      simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- Hanna's conjecture for A386655: for `n ≥ 6`, `a(n) mod 6` runs through
`[1, 0, 3, 0, 3, 2]` periodically, starting at `n = 6`. -/
theorem result : statement := by
  intro n hn
  have h3 := a_mod3 n hn
  have h2 := a_mod2 n (by omega)
  rw [ZMod.intCast_eq_intCast_iff'] at h3 h2
  push_cast at h3 h2
  rw [show (n - 6) % 6 = n % 6 by omega]
  have h6 : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize hr : n % 6 = r at h3 h6 ⊢
  interval_cases r <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at h3 ⊢ <;> omega

end Math0.Frontier.A386655

#math0_settles Math0.Frontier.A386655.result Math0.Statements.A386655.statement
