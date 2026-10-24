/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A086004
import Math0.Audit

/-!
# There are no 5-Rotation Cycle Primes (A086004, Conjecture 2)

We prove Seggelin's Conjecture 2: no prime `p` has `rotAdd^[j] p` prime for all
`j = 1, …, 5`, where `rotAdd n = n + rot n` is the rotate-and-add map of A086002.

**Even digit counts.** If `n` has `2k ≥ 2` digits then
`rotAdd n = (⌊n/10^k⌋ + n mod 10^k)·(10^k + 1)` (R. J. Mathar). If this is prime, the first factor
is `1`, which forces `n = 10^k`, not prime. So a prime `n` with `rotAdd n` prime has an odd
number `2m + 1` of digits (`odd_range`).

**Odd digit counts.** Put `P = 10^m` and write `n = X·10P + M·P + Y` with `Y < P`, `M < 10`
(`M` the centre digit). Then `rot n = Y·10P + M·P + X` and
`rotAdd n = S·10P + 2M·P + S` with `S = X + Y` (`rotAdd_odd`). Since `rot n < 10^(2m+1)`, the
number of digits grows by at most one per step, so along a chain of primes
`p, rotAdd p, …, rotAdd^[5] p` the first five terms all have the same `2m + 1` digits
(`stay`). When `rotAdd n` keeps `2m + 1` digits, `S < P`, so the centre digit of `rotAdd n` is
`2M mod 10`; and if `M ≤ 4` then `rotAdd n = S·10P + 2M·P + S` is fixed by `rot`, so the next
term is `2·rotAdd n`, which is not prime (`mid`).

**The centre digits.** Hence the centre digits `M₀, M₁, M₂, M₃` of the first four terms are all
`≥ 5` and satisfy `M_{j+1} = 2M_j mod 10`. But `M₀ ≥ 5`, `M₁ = 2M₀ − 10 ≥ 5` force `M₀ ∈ {8, 9}`,
`M₂ ≥ 5` forces `M₀ = 9`, and then `M₁ = 8`, `M₂ = 6`, `M₃ = 2 < 5`, a contradiction.
-/

namespace Math0.Frontier.A086004
open Math0.Statements.A086004

/-- Block arithmetic: for `S < P`, `S·10P + K·P + S` has remainder `S` and quotient `10S + K`
modulo/by `P`. -/
private lemma blocks {P S K : ℕ} (hP : 0 < P) (hS : S < P) :
    (S * (P * 10) + K * P + S) % P = S ∧ (S * (P * 10) + K * P + S) / P = 10 * S + K := by
  have e : S * (P * 10) + K * P + S = S + P * (10 * S + K) := by ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hS, Nat.add_mul_div_left _ _ hP,
    Nat.div_eq_of_lt hS]
  simp

/-- For `n` with `2m + 1` digits, `rot n = Y·10^(m+1) + M·10^m + X` where `Y = n mod 10^m`,
`M` is the centre digit and `X = ⌊n/10^(m+1)⌋`. -/
private lemma rot_odd {m n : ℕ} (h1 : 10 ^ (2 * m) ≤ n) (h2 : n < 10 ^ (2 * m + 1)) :
    rot n = n % 10 ^ m * (10 ^ m * 10) + n / 10 ^ m % 10 * 10 ^ m + n / (10 ^ m * 10) := by
  have hlen : (Nat.digits 10 n).length = 2 * m + 1 := length_digits_eq h1 h2
  unfold rot
  simp only [hlen]
  have e1 : (2 * m + 1) / 2 = m := by omega
  have e2 : 2 * m + 1 - m = m + 1 := by omega
  rw [e1, e2, show m + 1 - m = 1 by omega, pow_succ, pow_one]

/-- For `n` with `2k` digits, `rotAdd n = (⌊n/10^k⌋ + n mod 10^k)·(10^k + 1)` (R. J. Mathar). -/
private lemma rotAdd_even {k n : ℕ} (hlen : (Nat.digits 10 n).length = 2 * k) :
    rotAdd n = (n / 10 ^ k + n % 10 ^ k) * (10 ^ k + 1) := by
  unfold rotAdd rot
  simp only [hlen]
  have e1 : 2 * k / 2 = k := by omega
  have e2 : 2 * k - k = k := by omega
  rw [e1, e2, Nat.sub_self, pow_zero, Nat.mod_one, zero_mul, add_zero]
  have := Nat.div_add_mod n (10 ^ k)
  nth_rewrite 1 [← this]
  ring

/-- If `n` and `rotAdd n` are prime then `n` has an odd number `2m + 1` of digits. -/
private lemma odd_range {n : ℕ} (hn : n.Prime) (hf : (rotAdd n).Prime) :
    ∃ m, 10 ^ (2 * m) ≤ n ∧ n < 10 ^ (2 * m + 1) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (Nat.digits 10 n).length
  · exfalso
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp only [mul_zero, List.length_eq_zero_iff] at hk
        exact absurd hk (Nat.digits_ne_nil_iff_ne_zero.mpr hn0)
      · exact h
    have hlo : 10 ^ (2 * k - 1) ≤ n := (Nat.lt_digits_length_iff (by norm_num) n).1 (by omega)
    have hP : 10 ^ k ≤ n := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hlo
    rw [rotAdd_even hk, Nat.prime_mul_iff] at hf
    rcases hf with ⟨-, h⟩ | ⟨-, h⟩
    · have : 0 < 10 ^ k := by positivity
      omega
    · have hq : 1 ≤ n / 10 ^ k := (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa using hP)
      have hr : n % 10 ^ k = 0 := by omega
      have h10 : 10 ∣ n :=
        dvd_trans (dvd_pow_self 10 (by omega)) (Nat.dvd_of_mod_eq_zero hr)
      have h2 : 2 ∣ n := dvd_trans (by norm_num) h10
      have h10' : 10 ≤ 10 ^ k := by
        calc 10 = 10 ^ 1 := by norm_num
          _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
      rcases hn.eq_one_or_self_of_dvd 2 h2 with e | e <;> omega
  · refine ⟨k, (Nat.lt_digits_length_iff (by norm_num) n).1 (by omega), ?_⟩
    rw [← hk]
    exact Nat.lt_base_pow_length_digits (by norm_num)

/-- `n = ⌊n/10P⌋·10P + (⌊n/P⌋ mod 10)·P + n mod P`. -/
private lemma decomp (P n : ℕ) : n = n / (P * 10) * (P * 10) + n / P % 10 * P + n % P := by
  have h1 := Nat.div_add_mod n P
  have h2 := Nat.div_add_mod (n / P) 10
  rw [Nat.div_div_eq_div_mul] at h2
  calc n = P * (n / P) + n % P := h1.symm
    _ = P * (10 * (n / (P * 10)) + n / P % 10) + n % P := by rw [h2]
    _ = _ := by ring

/-- For `n` with `2m + 1` digits, `rotAdd n = S·10^(m+1) + 2M·10^m + S` with
`S = ⌊n/10^(m+1)⌋ + n mod 10^m` and `M` the centre digit. -/
private lemma rotAdd_odd {m n : ℕ} (h1 : 10 ^ (2 * m) ≤ n) (h2 : n < 10 ^ (2 * m + 1)) :
    rotAdd n = (n / (10 ^ m * 10) + n % 10 ^ m) * (10 ^ m * 10) +
      2 * (n / 10 ^ m % 10) * 10 ^ m + (n / (10 ^ m * 10) + n % 10 ^ m) := by
  unfold rotAdd
  rw [rot_odd h1 h2]
  nth_rewrite 1 [decomp (10 ^ m) n]
  ring

/-- For `n` with `2m + 1` digits, `rot n < 10^(2m+1)`. -/
private lemma rot_lt {m n : ℕ} (h1 : 10 ^ (2 * m) ≤ n) (h2 : n < 10 ^ (2 * m + 1)) :
    rot n < 10 ^ (2 * m + 1) := by
  rw [rot_odd h1 h2]
  set P := 10 ^ m with hP
  have hP0 : 0 < P := by positivity
  have e : 10 ^ (2 * m + 1) = P * (P * 10) := by rw [hP]; ring
  rw [e] at h2 ⊢
  have hX : n / (P * 10) < P := (Nat.div_lt_iff_lt_mul (by positivity)).2 h2
  have hY : n % P < P := Nat.mod_lt _ hP0
  have hM : n / P % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have a1 : (n % P + 1) * (P * 10) ≤ P * (P * 10) := Nat.mul_le_mul_right _ hY
  have a2 : n / P % 10 * P ≤ 9 * P := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- If `n` has `2m + 1` digits and `rotAdd n`, `rotAdd (rotAdd n)` are prime, then `rotAdd n`
still has `2m + 1` digits (it cannot reach `2m + 3` digits, and `2m + 2` is excluded by
`odd_range`). -/
private lemma stay {m n : ℕ} (h1 : 10 ^ (2 * m) ≤ n) (h2 : n < 10 ^ (2 * m + 1))
    (hp1 : (rotAdd n).Prime) (hp2 : (rotAdd (rotAdd n)).Prime) :
    rotAdd n < 10 ^ (2 * m + 1) := by
  obtain ⟨m', h1', h2'⟩ := odd_range hp1 hp2
  have hr := rot_lt h1 h2
  have hup : rotAdd n < 10 ^ (2 * m + 2) := by
    have : 10 ^ (2 * m + 2) = 10 * 10 ^ (2 * m + 1) := by ring
    unfold rotAdd
    omega
  rcases le_or_gt m' m with h | h
  · exact lt_of_lt_of_le h2' (Nat.pow_le_pow_right (by norm_num) (by omega))
  · have := Nat.pow_le_pow_right (show 0 < 10 by norm_num) (show 2 * m + 2 ≤ 2 * m' by omega)
    omega

/-- If `n` and `rotAdd n` both have `2m + 1` digits, the centre digit of `rotAdd n` is twice the
centre digit `M` of `n` modulo `10`, and if `M < 5` then `rot` fixes `rotAdd n`, so
`rotAdd (rotAdd n) = 2·rotAdd n`. -/
private lemma mid {m n : ℕ} (h1 : 10 ^ (2 * m) ≤ n) (h2 : n < 10 ^ (2 * m + 1))
    (h3 : rotAdd n < 10 ^ (2 * m + 1)) :
    rotAdd n / 10 ^ m % 10 = 2 * (n / 10 ^ m % 10) % 10 ∧
      (n / 10 ^ m % 10 < 5 → rotAdd (rotAdd n) = 2 * rotAdd n) := by
  have e := rotAdd_odd h1 h2
  have h1' : 10 ^ (2 * m) ≤ rotAdd n := le_trans h1 (Nat.le_add_right _ _)
  have hr := rot_odd h1' h3
  set P := 10 ^ m with hP
  have hP0 : 0 < P := by positivity
  set S := n / (P * 10) + n % P with hS
  set M := n / P % 10 with hM
  have eP : 10 ^ (2 * m + 1) = P * 10 * P := by rw [hP]; ring
  have hSP : S < P := by
    rw [eP, e] at h3
    have : S * (P * 10) < P * (P * 10) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  obtain ⟨hmod, hdiv⟩ := blocks (K := 2 * M) hP0 hSP
  rw [← e] at hmod hdiv
  refine ⟨by rw [hdiv]; omega, fun hM5 => ?_⟩
  have hdiv2 : rotAdd n / (P * 10) = S := by
    rw [← Nat.div_div_eq_div_mul, hdiv]
    omega
  have hmid : (10 * S + 2 * M) % 10 = 2 * M := by omega
  show rotAdd n + rot (rotAdd n) = 2 * rotAdd n
  rw [hr, hmod, hdiv, hdiv2, hmid, e]
  ring

/-- Twice a prime is not prime. -/
private lemma not_prime_two_mul {x : ℕ} (hx : x.Prime) : ¬ (2 * x).Prime := by
  intro h2
  rcases Nat.prime_mul_iff.1 h2 with ⟨_, e⟩ | ⟨_, e⟩
  · exact hx.ne_one e
  · norm_num at e

/-- Conjecture 2 of A086004 holds: there are no 5-Rotation Cycle Primes. -/
theorem result : statement := by
  rintro p ⟨h0, h⟩
  have p1 : (rotAdd p).Prime := h 1 (by norm_num) (by norm_num)
  have p2 : (rotAdd (rotAdd p)).Prime := h 2 (by norm_num) (by norm_num)
  have p3 : (rotAdd (rotAdd (rotAdd p))).Prime := h 3 (by norm_num) (by norm_num)
  have p4 : (rotAdd (rotAdd (rotAdd (rotAdd p)))).Prime := h 4 (by norm_num) (by norm_num)
  have p5 : (rotAdd (rotAdd (rotAdd (rotAdd (rotAdd p))))).Prime :=
    h 5 (by norm_num) (by norm_num)
  obtain ⟨m, l0, u0⟩ := odd_range h0 p1
  have u1 := stay l0 u0 p1 p2
  have l1 : 10 ^ (2 * m) ≤ rotAdd p := le_trans l0 (Nat.le_add_right _ _)
  have u2 := stay l1 u1 p2 p3
  have l2 : 10 ^ (2 * m) ≤ rotAdd (rotAdd p) := le_trans l1 (Nat.le_add_right _ _)
  have u3 := stay l2 u2 p3 p4
  have l3 : 10 ^ (2 * m) ≤ rotAdd (rotAdd (rotAdd p)) := le_trans l2 (Nat.le_add_right _ _)
  have u4 := stay l3 u3 p4 p5
  obtain ⟨a0, b0⟩ := mid l0 u0 u1
  obtain ⟨a1, b1⟩ := mid l1 u1 u2
  obtain ⟨a2, b2⟩ := mid l2 u2 u3
  obtain ⟨-, b3⟩ := mid l3 u3 u4
  have c0 : 5 ≤ p / 10 ^ m % 10 := by
    by_contra hc
    exact not_prime_two_mul p1 (b0 (by omega) ▸ p2)
  have c1 : 5 ≤ rotAdd p / 10 ^ m % 10 := by
    by_contra hc
    exact not_prime_two_mul p2 (b1 (by omega) ▸ p3)
  have c2 : 5 ≤ rotAdd (rotAdd p) / 10 ^ m % 10 := by
    by_contra hc
    exact not_prime_two_mul p3 (b2 (by omega) ▸ p4)
  have c3 : 5 ≤ rotAdd (rotAdd (rotAdd p)) / 10 ^ m % 10 := by
    by_contra hc
    exact not_prime_two_mul p4 (b3 (by omega) ▸ p5)
  have c4 : p / 10 ^ m % 10 < 10 := Nat.mod_lt _ (by norm_num)
  generalize p / 10 ^ m % 10 = M0 at a0 c0 c4
  generalize rotAdd p / 10 ^ m % 10 = M1 at a0 a1 c1
  generalize rotAdd (rotAdd p) / 10 ^ m % 10 = M2 at a1 a2 c2
  generalize rotAdd (rotAdd (rotAdd p)) / 10 ^ m % 10 = M3 at a2 c3
  interval_cases M0 <;> omega

end Math0.Frontier.A086004

#math0_settles Math0.Frontier.A086004.result Math0.Statements.A086004.statement
