/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A175385
import Math0.Audit

/-!
# `∑_{i=1..n} C(2n-i-1, i-1)/i` is never an integer for `n > 1` (A175385)

We prove the Shevelev–Seidov conjecture from OEIS A175385.

**Step 1 (closed form).** From `(2n-i)·C(2n-i-1,i-1) = i·C(2n-i,i)` we get
`2n·C(2n-i-1,i-1)/i = C(2n-i,i) + C(2n-i-1,i-1)`. Summing, and using the diagonal sums
`F(m+1) = ∑_k C(m-k,k)` of Pascal's triangle (`Nat.fib_succ_eq_sum_choose`), gives
`2n·S(n) + 1 = F(2n+1) + F(2n-1) = L(2n)` (the Lucas number). So if `S(n) = k ∈ ℤ` then
`L(2n) = 2nk + 1`.

**Step 2 (Lucas numbers in a ring).** In any commutative ring with `α² = α + 1` we have
`α^(j+1) = F(j+1)α + F(j)`, and `β = 1 - α` satisfies the same equation, so
`L(2n) = α^(2n) + β^(2n)` there.

**Step 3 (contradiction).**
* `n` even: `4 ∣ 2n`, but `F` has period 6 mod 4 and `L(2n) mod 4 ∈ {2, 3}`.
* `n` odd with smallest prime factor `p = 5`: in `ZMod 5`, `α = β = 3`, so
  `L(2n) = 2·9^n = -2 ≠ 1`.
* `n` odd with smallest prime factor `p ∉ {2, 5}`: take `α = (1+√5)/2` in the algebraic closure
  `K` of `ZMod p`. Frobenius permutes the roots of `X² - X - 1`, so `α^(p²) = α` and
  `α^(p²-1) = 1`. From `L(2n) = 1` in `K` and `αβ = -1`, `x = α^(2n)` satisfies
  `x² - x + 1 = 0`, hence `α^(6n) = -1` and `α^(12n) = 1`. Every prime factor of `p² - 1` is
  smaller than `p`, so `gcd(n, p² - 1) = 1`, the order of `α` divides `12`, and since `n` is odd,
  `α^6 = -1`. With `α² = α + 1` this forces `20 = 0` in `K`, i.e. `p ∣ 20`, a contradiction.
-/

namespace Math0.Frontier.A175385
open Math0.Statements.A175385
open Finset

/-- `F(m+1) = ∑_{k ≤ m} C(m-k, k)`. -/
private lemma fib_succ_eq_sum_range (m : ℕ) :
    Nat.fib (m + 1) = ∑ k ∈ range (m + 1), Nat.choose (m - k) k := by
  rw [Nat.fib_succ_eq_sum_choose, ← Finset.Nat.sum_antidiagonal_swap]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Nat.choose j i) m

/-- Truncation: if `m < 2N` then `F(m+1) = ∑_{k < N} C(m-k, k)`. -/
private lemma fib_succ_eq_sum_range' (m N : ℕ) (h : m < 2 * N) :
    Nat.fib (m + 1) = ∑ k ∈ range N, Nat.choose (m - k) k := by
  have h1 : ∑ k ∈ range N, Nat.choose (m - k) k =
      ∑ k ∈ range (N + m + 1), Nat.choose (m - k) k := by
    apply Finset.sum_subset
    · intro x hx; simp only [mem_range] at hx ⊢; omega
    · intro x hx hx'
      simp only [mem_range] at hx hx'
      exact Nat.choose_eq_zero_of_lt (by omega)
  have h2 : ∑ k ∈ range (m + 1), Nat.choose (m - k) k =
      ∑ k ∈ range (N + m + 1), Nat.choose (m - k) k := by
    apply Finset.sum_subset
    · intro x hx; simp only [mem_range] at hx ⊢; omega
    · intro x hx hx'
      simp only [mem_range] at hx hx'
      exact Nat.choose_eq_zero_of_lt (by omega)
  rw [h1, ← h2, fib_succ_eq_sum_range]

/-- The termwise identity `2n·C(2n-i-1,i-1)/i = C(2n-i,i) + C(2n-i-1,i-1)`, written with
`n = m + 1` and `i = j + 1`. -/
private lemma term_identity (m j : ℕ) (hj : j ≤ m) :
    (2 * ((m : ℚ) + 1)) * (((Nat.choose (2 * m - j) j : ℕ) : ℚ) / ((j : ℚ) + 1)) =
      ((Nat.choose (2 * m + 1 - j) (j + 1) : ℕ) : ℚ) + ((Nat.choose (2 * m - j) j : ℕ) : ℚ) := by
  have h := Nat.add_one_mul_choose_eq (2 * m - j) j
  have he : 2 * m - j + 1 = 2 * m + 1 - j := by omega
  rw [he] at h
  have hq : ((2 * m + 1 - j : ℕ) : ℚ) * (Nat.choose (2 * m - j) j : ℚ) =
      (Nat.choose (2 * m + 1 - j) (j + 1) : ℚ) * ((j : ℚ) + 1) := by exact_mod_cast h
  have hc : ((2 * m + 1 - j : ℕ) : ℚ) = 2 * (m : ℚ) + 1 - j := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hc] at hq
  have hj1 : (j : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  linear_combination hq

/-- Reindex `S (m+1)` as a sum over `j = i - 1 ∈ [0, m]`. -/
private lemma S_succ (m : ℕ) :
    S (m + 1) = ∑ j ∈ range (m + 1), ((Nat.choose (2 * m - j) j : ℕ) : ℚ) / ((j : ℚ) + 1) := by
  unfold S
  symm
  apply Finset.sum_nbij' (· + 1) (· - 1)
  · intro x hx; simp only [mem_range, mem_Icc] at hx ⊢; omega
  · intro x hx; simp only [mem_range, mem_Icc] at hx ⊢; omega
  · intro x hx; simp
  · intro x hx; simp only [mem_Icc] at hx ⊢; omega
  · intro x hx
    simp only [mem_range] at hx
    have e1 : 2 * (m + 1) - (x + 1) - 1 = 2 * m - x := by omega
    rw [e1, Nat.add_sub_cancel]
    push_cast
    rfl

/-- The closed form `2n·S(n) + 1 = F(2n+1) + F(2n-1)` (with `n = m + 1`). -/
private lemma main_identity (m : ℕ) :
    2 * ((m : ℚ) + 1) * S (m + 1) + 1 = (Nat.fib (2 * m + 3) : ℚ) + Nat.fib (2 * m + 1) := by
  rw [S_succ, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j hj => term_identity m j (by simp at hj; omega))]
  rw [Finset.sum_add_distrib]
  have hA : (Nat.fib (2 * m + 3) : ℚ) =
      ∑ j ∈ range (m + 1), ((Nat.choose (2 * m + 1 - j) (j + 1) : ℕ) : ℚ) + 1 := by
    have := fib_succ_eq_sum_range' (2 * m + 2) (m + 2) (by omega)
    rw [Finset.sum_range_succ'] at this
    rw [show 2 * m + 3 = 2 * m + 2 + 1 by ring, this]
    push_cast
    congr 1
  have hB : (Nat.fib (2 * m + 1) : ℚ) =
      ∑ j ∈ range (m + 1), ((Nat.choose (2 * m - j) j : ℕ) : ℚ) := by
    rw [fib_succ_eq_sum_range' (2 * m) (m + 1) (by omega)]; push_cast; rfl
  rw [hA, hB]; ring

/-- If `α² = α + 1` in a commutative ring then `α^(j+1) = F(j+1)·α + F(j)`. -/
private lemma pow_eq_fib {R : Type*} [CommRing R] (α : R) (hα : α ^ 2 = α + 1) (j : ℕ) :
    α ^ (j + 1) = (Nat.fib (j + 1) : R) * α + Nat.fib j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih, Nat.fib_add_two]
    push_cast
    linear_combination (Nat.fib (j + 1) : R) * hα

/-- If `α² = α + 1` then `F(2m+3) + F(2m+1) = α^(2m+2) + (1-α)^(2m+2)` (a Lucas number). -/
private lemma lucas {R : Type*} [CommRing R] (α : R) (hα : α ^ 2 = α + 1) (m : ℕ) :
    ((Nat.fib (2 * m + 3) + Nat.fib (2 * m + 1) : ℕ) : R) =
      α ^ (2 * (m + 1)) + (1 - α) ^ (2 * (m + 1)) := by
  have hβ : (1 - α) ^ 2 = (1 - α) + 1 := by linear_combination hα
  have e : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
  rw [e, pow_eq_fib α hα, pow_eq_fib (1 - α) hβ]
  have h3 : Nat.fib (2 * m + 3) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 1 + 1) :=
    Nat.fib_add_two
  rw [h3]
  push_cast
  ring

/-- In a field of characteristic `p`, a root `α` of `X² - X - 1` satisfies `α^(p²-1) = 1`:
Frobenius sends `α` to a root, i.e. to `α` or `1 - α`, and in both cases `α^(p²) = α`. -/
private lemma frob {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (α : K)
    (hα : α ^ 2 = α + 1) : α ^ (p ^ 2 - 1) = 1 := by
  have hy : (α ^ p) ^ 2 = α ^ p + 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hα, add_pow_char, one_pow]
  have hprod : (α ^ p - α) * (α ^ p - (1 - α)) = 0 := by linear_combination hy - hα
  have hpp : α ^ (p ^ 2) = α := by
    rw [sq, pow_mul]
    rcases mul_eq_zero.mp hprod with h | h
    · rw [sub_eq_zero.mp h, sub_eq_zero.mp h]
    · rw [sub_eq_zero.mp h, sub_pow_char, one_pow, sub_eq_zero.mp h]; ring
  have hα0 : α ≠ 0 := by rintro rfl; norm_num at hα
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have : α ^ (p ^ 2 - 1) * α = 1 * α := by
    rw [← pow_succ, Nat.sub_add_cancel hp1, hpp, one_mul]
  exact mul_right_cancel₀ hα0 this

/-- The only primes dividing `20` are `2` and `5`. -/
private lemma prime_dvd_twenty (p : ℕ) (hp : p.Prime) (h : p ∣ 20) : p = 2 ∨ p = 5 := by
  have hle : p ≤ 20 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> simp_all <;> norm_num at hp

/-- The core argument: in a field of characteristic `p ∉ {2, 5}` with `α² = α + 1`, if `N` is
odd and coprime to `p² - 1` then `α^(2N) + (1-α)^(2N) ≠ 1`. -/
private lemma field_part {K : Type*} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (α : K) (hα : α ^ 2 = α + 1) (N : ℕ) (hN : Odd N)
    (hcop : Nat.Coprime N (p ^ 2 - 1)) : α ^ (2 * N) + (1 - α) ^ (2 * N) ≠ 1 := by
  intro h
  set x := α ^ (2 * N) with hx
  have hprod : x * (1 - α) ^ (2 * N) = 1 := by
    rw [hx, ← mul_pow, show α * (1 - α) = -1 by linear_combination -hα, pow_mul, neg_one_sq,
      one_pow]
  have hx2 : x ^ 2 - x + 1 = 0 := by linear_combination x * h - hprod
  have h6 : α ^ (6 * N) = -1 := by
    have : α ^ (6 * N) = x ^ 3 := by rw [hx, ← pow_mul]; ring_nf
    rw [this]; linear_combination (x + 1) * hx2
  have h12 : α ^ (12 * N) = 1 := by
    rw [show 12 * N = 6 * N * 2 by ring, pow_mul, h6]; norm_num
  have hd1 : orderOf α ∣ 12 * N := orderOf_dvd_of_pow_eq_one h12
  have hd2 : orderOf α ∣ p ^ 2 - 1 := orderOf_dvd_of_pow_eq_one (frob p α hα)
  have hcop' : Nat.Coprime (orderOf α) N := (hcop.coprime_dvd_right hd2).symm
  have hd3 : orderOf α ∣ 12 := hcop'.dvd_of_dvd_mul_right hd1
  have h12' : α ^ 12 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd3
  obtain ⟨t, rfl⟩ := hN
  have h6' : α ^ 6 = -1 := by
    rw [show 6 * (2 * t + 1) = 12 * t + 6 by ring, pow_add, pow_mul, h12', one_pow,
      one_mul] at h6
    exact h6
  have h20 : (20 : K) = 0 := by
    linear_combination (14 - 8 * α) * h6' +
      (8 * α ^ 5 - 6 * α ^ 4 + 2 * α ^ 3 - 4 * α ^ 2 - 2 * α - 6) * hα
  have h20' : ((20 : ℕ) : K) = 0 := by exact_mod_cast h20
  rw [CharP.cast_eq_zero_iff K p] at h20'
  rcases prime_dvd_twenty p hp.out h20' with h' | h' <;> contradiction

/-- Fibonacci numbers have period `6` modulo `4`. -/
private lemma fib_add_six_mod (j : ℕ) : Nat.fib (j + 6) % 4 = Nat.fib j % 4 := by
  have h := Nat.fib_add 5 j
  rw [show 5 + j + 1 = j + 6 by ring, show Nat.fib 5 = 5 by rfl,
    show Nat.fib (5 + 1) = 8 by rfl] at h
  omega

/-- `F(j) ≡ F(j mod 6) (mod 4)`. -/
private lemma fib_mod_four (j : ℕ) : Nat.fib j % 4 = Nat.fib (j % 6) % 4 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < 6
    · rw [Nat.mod_eq_of_lt hj]
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 6 := ⟨j - 6, by omega⟩
      rw [fib_add_six_mod, ih i (by omega), show (i + 6) % 6 = i % 6 by omega]

/-- For `m` odd (`n = m + 1` even), `L(2n) = F(2m+3) + F(2m+1)` is `2` or `3` modulo `4`. -/
private lemma T_mod_four (m : ℕ) (hm : m % 2 = 1) :
    (Nat.fib (2 * m + 3) + Nat.fib (2 * m + 1)) % 4 = 2 ∨
      (Nat.fib (2 * m + 3) + Nat.fib (2 * m + 1)) % 4 = 3 := by
  rw [Nat.add_mod, fib_mod_four (2 * m + 3), fib_mod_four (2 * m + 1)]
  have : m % 6 = 1 ∨ m % 6 = 3 ∨ m % 6 = 5 := by omega
  rcases this with h | h | h
  · rw [show (2 * m + 3) % 6 = 5 by omega, show (2 * m + 1) % 6 = 3 by omega]; decide
  · rw [show (2 * m + 3) % 6 = 3 by omega, show (2 * m + 1) % 6 = 1 by omega]; decide
  · rw [show (2 * m + 3) % 6 = 1 by omega, show (2 * m + 1) % 6 = 5 by omega]; decide

/-- An odd `n > 1` is coprime to `p² - 1`, where `p` is its smallest prime factor: every prime
factor of `p² - 1 = (p-1)(p+1)` is less than `p`. -/
private lemma coprime_minFac (n : ℕ) (hn : 1 < n) (hodd : Odd n) :
    Nat.Coprime n (n.minFac ^ 2 - 1) := by
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hp2 : 2 ≤ n.minFac := hp.two_le
  obtain ⟨r, hr⟩ : ∃ r, n.minFac = r + 1 := ⟨n.minFac - 1, by omega⟩
  have hpodd : n.minFac % 2 = 1 := by
    have := Odd.of_dvd_nat hodd (Nat.minFac_dvd n)
    exact Nat.odd_iff.mp this
  have hsq : n.minFac ^ 2 - 1 = r * (r + 2) := by
    rw [hr, show (r + 1) ^ 2 = r * (r + 2) + 1 by ring, Nat.add_sub_cancel]
  rw [hsq]
  apply Nat.coprime_of_dvd
  intro q hq hqn hqr
  have hqge : n.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqn
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (Odd.of_dvd_nat hodd hqn)
  rcases (Nat.Prime.dvd_mul hq).mp hqr with h | h
  · have : q ≤ r := Nat.le_of_dvd (by omega) h
    omega
  · have : q ≤ r + 2 := Nat.le_of_dvd (by omega) h
    have hq' : q = r + 1 ∨ q = r + 2 := by omega
    rcases hq' with hq' | hq'
    · rw [hq'] at h
      have h1 : r + 1 ∣ 1 := (Nat.dvd_add_right (dvd_refl (r + 1))).mp h
      have := Nat.le_of_dvd (by norm_num) h1
      omega
    · omega

/-- **A175385.** For every `n > 1`, `∑_{i=1}^{n} C(2n-i-1, i-1)/i` is not an integer. -/
theorem result : statement := by
  intro n hn ⟨k, hk⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hid := main_identity m
  rw [hk] at hid
  have hZ : 2 * ((m : ℤ) + 1) * k + 1 = ((Nat.fib (2 * m + 3) + Nat.fib (2 * m + 1) : ℕ) : ℤ) := by
    push_cast
    exact_mod_cast hid
  rcases Nat.even_or_odd (m + 1) with hev | hodd
  · obtain ⟨t, ht⟩ := hev
    have hmod := T_mod_four m (by omega)
    have h4 : ((Nat.fib (2 * m + 3) + Nat.fib (2 * m + 1) : ℕ) : ℤ) = 4 * (t * k) + 1 := by
      rw [← hZ]
      have : ((m : ℤ) + 1) = 2 * t := by exact_mod_cast (by omega : m + 1 = 2 * t)
      rw [this]; ring
    omega
  · have key : ∀ (R : Type) [CommRing R] (q : ℕ) [CharP R q], q ∣ m + 1 →
        ((Nat.fib (2 * m + 3) + Nat.fib (2 * m + 1) : ℕ) : R) = 1 := by
      intro R _ q _ hq
      have h1 : ((m + 1 : ℕ) : R) = 0 := (CharP.cast_eq_zero_iff R q _).mpr hq
      have h2 := congrArg (fun z : ℤ => (z : R)) hZ
      simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one] at h2
      push_cast at h1 h2 ⊢
      rw [← h2, h1]; ring
    have hp : (m + 1).minFac.Prime := Nat.minFac_prime (by omega)
    have hpd : (m + 1).minFac ∣ m + 1 := Nat.minFac_dvd _
    have hp2 : (m + 1).minFac ≠ 2 := by
      intro h2
      rw [h2] at hpd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
    by_cases hp5 : (m + 1).minFac = 5
    · rw [hp5] at hpd
      have h := key (ZMod 5) 5 hpd
      rw [lucas (3 : ZMod 5) (by decide) m] at h
      have h13 : (1 - 3 : ZMod 5) = 3 := by decide
      have h9 : (3 : ZMod 5) ^ 2 = -1 := by decide
      rw [h13, pow_mul, h9, Odd.neg_one_pow hodd] at h
      revert h; decide
    · set p := (m + 1).minFac with hpdef
      have := Fact.mk hp
      obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (5 : AlgebraicClosure (ZMod p))
      have h2 : (2 : AlgebraicClosure (ZMod p)) ≠ 0 := by
        intro h
        have h' : ((2 : ℕ) : AlgebraicClosure (ZMod p)) = 0 := by exact_mod_cast h
        rw [CharP.cast_eq_zero_iff _ p] at h'
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      have hα : ((1 + s) / 2) ^ 2 = (1 + s) / 2 + 1 := by
        field_simp
        linear_combination -hs
      apply field_part p hp2 hp5 ((1 + s) / 2) hα (m + 1) hodd
        (coprime_minFac (m + 1) (by omega) hodd)
      rw [← lucas _ hα m]
      exact key _ p hpd

end Math0.Frontier.A175385

#math0_settles Math0.Frontier.A175385.result Math0.Statements.A175385.statement
