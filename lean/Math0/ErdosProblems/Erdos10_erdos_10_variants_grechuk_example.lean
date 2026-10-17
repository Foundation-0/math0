/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«10»
import Math0.Audit

/-!
# Erdős Problem 10: Grechuk's example 1117175146

Erdős Problem 10 asks whether every large integer is a prime plus a bounded number of powers
of two. Bogdan Grechuk observed that `1117175146` is not the sum of a prime and at most three
powers of two; this file proves exactly the upstream statement
`1117175146 ∉ sumPrimeAndTwoPows 3`. Any power of two `≤ 1117175146` is `2 ^ e` with `e ≤ 30`,
so it suffices to check, for every choice of at most three exponents in `[0, 30]` whose powers
sum to `s ≤ 1117175146`, that `1117175146 - s` has a proper divisor from an explicit list of 38
small primes (2 handles every even remainder; the odd remainders need primes up to 19391).
This finite certificate check is carried out by the Lean kernel (`decide +kernel`).
-/

namespace Math0.Erdos10

/-- Candidate small prime factors (2 plus every least prime factor that occurs). -/
def wit : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 37, 41, 47, 59, 61, 73, 79, 89, 97, 101, 103,
  107, 131, 163, 199, 211, 229, 257, 379, 547, 659, 877, 1381, 1481, 1699, 2099, 7283, 7703, 19391]

/-- `good m` certifies that `m` is not prime: either `m < 2`, or some listed `q ≥ 2` is a
proper divisor of `m`. -/
def good (m : ℕ) : Bool := m < 2 || wit.any (fun q => m % q == 0 && q < m)

/-- A certified number is not prime. -/
theorem not_prime_of_good {m : ℕ} (h : good m = true) : ¬ m.Prime := by
  intro hp
  unfold good at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have := hp.two_le
    simp at h
    omega
  · obtain ⟨q, hq, hq'⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hq'
    have hq2 : 2 ≤ q := by
      simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
    rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hq'.1) with h | h <;> omega


/-- Every sum of three powers of two not exceeding `1117175146` leaves a certified remainder. -/
def check3 : Bool :=
  (List.range 31).all fun x => (List.range 31).all fun y => (List.range 31).all fun z =>
    !(2 ^ x + 2 ^ y + 2 ^ z ≤ 1117175146) || good (1117175146 - (2 ^ x + 2 ^ y + 2 ^ z))

/-- Every sum of two powers of two not exceeding `1117175146` leaves a certified remainder. -/
def check2 : Bool :=
  (List.range 31).all fun x => (List.range 31).all fun y =>
    !(2 ^ x + 2 ^ y ≤ 1117175146) || good (1117175146 - (2 ^ x + 2 ^ y))

/-- Every power of two not exceeding `1117175146` leaves a certified remainder. -/
def check1 : Bool :=
  (List.range 31).all fun x => !(2 ^ x ≤ 1117175146) || good (1117175146 - 2 ^ x)

/-- Kernel verification of `check3`. -/
theorem check3_eq : check3 = true := by decide +kernel

/-- Kernel verification of `check2`. -/
theorem check2_eq : check2 = true := by decide +kernel

/-- Kernel verification of `check1`. -/
theorem check1_eq : check1 = true := by decide +kernel

/-- `1117175146` itself is certified (it is even and larger than 2). -/
theorem good_N : good 1117175146 = true := by decide +kernel

/-- An exponent whose power of two is at most `1117175146` is at most 30. -/
theorem exp_lt {x : ℕ} (h : 2 ^ x ≤ 1117175146) : x < 31 := by
  by_contra hx
  have : 2 ^ 31 ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at this
  omega

/-- Unpacked form of `check3_eq`: a three-term certificate for arbitrary exponents. -/
theorem spec3 {x y z : ℕ} (hs : 2 ^ x + 2 ^ y + 2 ^ z ≤ 1117175146) :
    good (1117175146 - (2 ^ x + 2 ^ y + 2 ^ z)) = true := by
  have := Nat.one_le_two_pow (n := x)
  have := Nat.one_le_two_pow (n := y)
  have := Nat.one_le_two_pow (n := z)
  have hx : x < 31 := exp_lt (by omega)
  have hy : y < 31 := exp_lt (by omega)
  have hz : z < 31 := exp_lt (by omega)
  have h := check3_eq
  unfold check3 at h
  rw [List.all_eq_true] at h
  have h := h x (List.mem_range.2 hx)
  rw [List.all_eq_true] at h
  have h := h y (List.mem_range.2 hy)
  rw [List.all_eq_true] at h
  have h := h z (List.mem_range.2 hz)
  simpa [hs] using h

/-- Unpacked form of `check2_eq`: a two-term certificate for arbitrary exponents. -/
theorem spec2 {x y : ℕ} (hs : 2 ^ x + 2 ^ y ≤ 1117175146) :
    good (1117175146 - (2 ^ x + 2 ^ y)) = true := by
  have := Nat.one_le_two_pow (n := x)
  have := Nat.one_le_two_pow (n := y)
  have hx : x < 31 := exp_lt (by omega)
  have hy : y < 31 := exp_lt (by omega)
  have h := check2_eq
  unfold check2 at h
  rw [List.all_eq_true] at h
  have h := h x (List.mem_range.2 hx)
  rw [List.all_eq_true] at h
  have h := h y (List.mem_range.2 hy)
  simpa [hs] using h

/-- Unpacked form of `check1_eq`: a one-term certificate for arbitrary exponents. -/
theorem spec1 {x : ℕ} (hs : 2 ^ x ≤ 1117175146) : good (1117175146 - 2 ^ x) = true := by
  have hx : x < 31 := exp_lt hs
  have h := check1_eq
  unfold check1 at h
  rw [List.all_eq_true] at h
  have h := h x (List.mem_range.2 hx)
  simpa [hs] using h

/-- Grechuk's observation: `1117175146` is not a prime plus at most three powers of two. -/
theorem erdos_10_grechuk_example : type_of% @Erdos10.erdos_10.variants.grechuk_example := by
  rintro ⟨p, pows, hp, hcard, h⟩
  induction pows using Quotient.inductionOn with
  | h l =>
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp at h
    exact not_prime_of_good (h ▸ good_N) hp
  · simp at h
    have hs : 2 ^ a ≤ 1117175146 := by omega
    exact not_prime_of_good (show p = 1117175146 - 2 ^ a by omega ▸ spec1 hs) hp
  · simp at h
    have hs : 2 ^ a + 2 ^ b ≤ 1117175146 := by omega
    exact not_prime_of_good (show p = 1117175146 - (2 ^ a + 2 ^ b) by omega ▸ spec2 hs) hp
  · simp at h
    have hs : 2 ^ a + 2 ^ b + 2 ^ c ≤ 1117175146 := by omega
    exact not_prime_of_good (show p = 1117175146 - (2 ^ a + 2 ^ b + 2 ^ c) by omega ▸ spec3 hs) hp
  · simp at hcard
    omega

end Math0.Erdos10

#math0_proves Math0.Erdos10.erdos_10_grechuk_example Erdos10.erdos_10.variants.grechuk_example
