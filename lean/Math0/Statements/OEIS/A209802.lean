/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A209802: positivity of the exponential Mertens function

Source: https://oeis.org/A209802, _Reinhard Zumkeller_, Mar 13 2012. Verbatim (COMMENTS):
> Analog of Mertens's function, A002321; conjecture: a(n) > 0.

The entry's name is "Partial sums of exponential Möbius function, A166234." (offset `1`).
A166234 is "The inverse of the constant 1 function under the exponential convolution (also
called the exponential Möbius function)", with the formula "Multiplicative, a(p^e) = mu(e) for
any prime power p^e (e>=1), where mu is the Möbius function A008683." (offset `1`).

## Encoding

* `muE n` is the exponential Möbius function `μ⁽ᵉ⁾(n) = ∏_{p^e ∥ n} μ(e)`, written with Mathlib's
  `Nat.factorization` and `ArithmeticFunction.moebius`: the product over the prime factors `p`
  of `n` of `μ` of the exponent of `p` in `n`. For `n = 1` it is the empty product `1`, as for any
  multiplicative function. (`muE 0 = 1` is never used.)
* `a n = ∑_{k=1}^{n} muE k` (OEIS offset `1`; `a 0 = 0` is the empty sum and is not a term of
  the sequence). The values are integers, so `a` is `ℤ`-valued: the sequence carries the keyword
  `nonn` only because of the very conjecture formalized here.
* `muE` and `a` are computable, but `Nat.factorization` and `moebius` do not reduce well in the
  kernel. For the kernel-checked data we therefore use a trial-division copy `aC` (prime divisors
  found by scanning `0, …, n`, exponents via `Nat.findGreatest`, `μ` via its values on prime
  powers) and prove `a = aC` (`a_eq_aC`) before running `decide +kernel`.
* The conjecture "a(n) > 0" is read for every index `n ≥ 1` of the sequence.
-/

namespace Math0.Statements.A209802

open ArithmeticFunction Finset

/-- The exponential Möbius function A166234: multiplicative with `μ⁽ᵉ⁾(p ^ e) = μ(e)`, i.e.
`μ⁽ᵉ⁾(n) = ∏_{p ∣ n prime} μ(v_p(n))`, where `v_p(n) = n.factorization p` is the exponent of
`p` in `n`. -/
def muE (n : ℕ) : ℤ := n.factorization.prod fun _ e => moebius e

/-- A209802: partial sums `a(n) = ∑_{k=1}^{n} μ⁽ᵉ⁾(k)` of the exponential Möbius function
(offset `1`). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Icc 1 n, muE k

/-! ### A kernel-friendly copy of the definition -/

/-- The exponent of `p` in `n` (for `p` prime, `n ≥ 1`): the largest `j ≤ n` with `p ^ j ∣ n`. -/
def expo (p n : ℕ) : ℕ := Nat.findGreatest (fun j => p ^ j ∣ n) n

/-- The prime divisors of `n`, found by scanning `0, …, n`. -/
def primeDivs (n : ℕ) : Finset ℕ := (range (n + 1)).filter fun p => p ∣ n ∧ p.Prime

/-- `∏_{p ∣ n prime} g (v_p(n))`, computed by trial division. -/
def prodPF (g : ℕ → ℤ) (n : ℕ) : ℤ := ∏ p ∈ primeDivs n, g (expo p n)

/-- The Möbius function, computed from its values `μ(p) = -1`, `μ(p ^ e) = 0` (`e ≥ 2`) on prime
powers. -/
def mobC (e : ℕ) : ℤ := if e = 0 then 0 else prodPF (fun f => if f = 1 then -1 else 0) e

/-- Trial-division copy of `muE`. -/
def muEC (n : ℕ) : ℤ := prodPF mobC n

/-- Trial-division copy of `a`. -/
def aC (n : ℕ) : ℤ := ∑ k ∈ Icc 1 n, muEC k

theorem primeDivs_eq {n : ℕ} (hn : n ≠ 0) : primeDivs n = n.primeFactors := by
  ext p
  simp only [primeDivs, mem_filter, mem_range, Nat.mem_primeFactors]
  constructor
  · rintro ⟨-, hd, hp⟩
    exact ⟨hp, hd, hn⟩
  · rintro ⟨hp, hd, -⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd), hd, hp⟩

theorem expo_eq {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : expo p n = n.factorization p := by
  unfold expo
  rw [Nat.findGreatest_eq_iff]
  refine ⟨(Nat.factorization_lt p hn).le, fun _ => (hp.pow_dvd_iff_le_factorization hn).2 le_rfl,
    ?_⟩
  intro j hj _ hd
  exact absurd ((hp.pow_dvd_iff_le_factorization hn).1 hd) (not_le.2 hj)

theorem prod_factorization_eq_prodPF (g : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) :
    (n.factorization.prod fun _ e => g e) = prodPF g n := by
  rw [Finsupp.prod, Nat.support_factorization, prodPF, primeDivs_eq hn]
  refine prod_congr rfl fun p hp => ?_
  rw [expo_eq (Nat.prime_of_mem_primeFactors hp) hn]

theorem moebius_eq_mobC (e : ℕ) : moebius e = mobC e := by
  rcases eq_or_ne e 0 with rfl | he
  · simp [mobC]
  rw [IsMultiplicative.multiplicative_factorization moebius isMultiplicative_moebius he, mobC,
    if_neg he, ← prod_factorization_eq_prodPF _ he, Finsupp.prod, Finsupp.prod]
  refine prod_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  exact moebius_apply_prime_pow hp'
    (hp'.factorization_pos_of_dvd he (Nat.dvd_of_mem_primeFactors hp)).ne'

theorem muE_eq_muEC (n : ℕ) : muE n = muEC n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [show muEC 0 = 1 by decide]
    simp [muE]
  · unfold muE muEC
    simp_rw [moebius_eq_mobC]
    exact prod_factorization_eq_prodPF mobC hn

theorem a_eq_aC : a = aC := funext fun _ => sum_congr rfl fun k _ => muE_eq_muEC k

/-! ### Sanity checks -/

/-- `muE` reproduces the 91 terms of A166234 listed in OEIS (kernel-checked). -/
theorem muE_data : (List.range 91).map (fun i => muE (i + 1)) =
    [1, 1, 1, -1, 1, 1, 1, -1, -1, 1, 1, -1, 1, 1, 1, 0, 1, -1, 1, -1, 1, 1, 1, -1, -1, 1, -1,
      -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, -1, 1, 1, 0, -1, -1, 1, -1, 1, -1,
      1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 0, 0, 1,
      1, -1, 1, 1, 1, -1, 1, -1, 1] := by
  rw [show muE = muEC from funext muE_eq_muEC]
  decide +kernel

/-- The definition reproduces all 72 terms of A209802 listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 72).map (fun i => a (i + 1)) =
    [1, 2, 3, 2, 3, 4, 5, 4, 3, 4, 5, 4, 5, 6, 7, 7, 8, 7, 8, 7, 8, 9, 10, 9, 8, 9, 8, 7, 8, 9,
      10, 9, 10, 11, 12, 13, 14, 15, 16, 15, 16, 17, 18, 17, 16, 17, 18, 18, 17, 16, 17, 16, 17,
      16, 17, 16, 17, 18, 19, 18, 19, 20, 19, 20, 21, 22, 23, 22, 23, 24, 25, 26] := by
  rw [a_eq_aC]
  decide +kernel

/-- The values `a(10) = 4` and `a(100) = 34` from the entry's comment (kernel-checked). -/
theorem a_ten_hundred : a 10 = 4 ∧ a 100 = 34 := by
  rw [a_eq_aC]
  decide +kernel

/-- Conjecture (Zumkeller, A209802): `a(n) > 0` for every `n ≥ 1`. -/
def statement : Prop := ∀ n : ℕ, 1 ≤ n → 0 < a n

end Math0.Statements.A209802
