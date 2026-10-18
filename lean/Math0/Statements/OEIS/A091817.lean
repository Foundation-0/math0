/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A091817: `(2*numerator(H(p-3)) - 3*denominator(H(p-3)))/p` is always an integer

Source: https://oeis.org/A091817, Mohammed Bouayoun and Ralf Stephan, Mar 07 2004 (proposed by
Leroy Quet). Verbatim:
> Leroy Quet conjectures that the terms are always integral. This is true for p < 3*10^4.

The entry's name is "(2*numerator(H(p-3)) -3*denominator(H(p-3)))/p with
H(m) = 1 + 1/2 + 1/3 + ...+ 1/m", with offset 1, and its PARI program runs over the primes
`p = 3, 5, 7, 11, …` (`forprime(p=3,100,…)`), so `a(1)` belongs to `p = 3`, `a(2)` to `p = 5`,
and in general `a(n)` belongs to the `(n+1)`-th prime.

## Encoding

* `H m = ∑_{k = 1..m} 1/k` in `ℚ` (`H 0 = 0`, as in PARI where the empty sum is `0`, with
  numerator `0` and denominator `1`). Mathlib's `Rat` is always in lowest terms with a positive
  denominator, so `(H m).num` and `(H m).den` are PARI's `numerator` and `denominator`.
* `term p = (2 * (H (p-3)).num - 3 * (H (p-3)).den) / p`, computed exactly in `ℚ`: the
  integrality of this quotient is the content of the conjecture, so the sequence is encoded as
  `ℚ`-valued and nothing is rounded.
* `primeAt i` is the `i`-th prime, 0-indexed (`primeAt 0 = 2`, `primeAt 1 = 3`, …), computed by a
  bounded search; `primeAt_eq_nth` proves `primeAt i = Nat.nth Nat.Prime i`. With offset 1,
  `a n = term (primeAt n)`: `a 1 = term 3`, `a 2 = term 5`, … (`a 0 = term 2` is outside the
  sequence and is never used).
* The data check reproduces all 18 listed terms (`p = 3, …, 67`).
* "The terms are always integral" is read as: for every index `n ≥ 1` (equivalently, for every
  prime `p ≥ 3`), the rational number `a n` is an integer, i.e. `p` divides
  `2*numerator(H(p-3)) - 3*denominator(H(p-3))` in `ℤ`.
-/

namespace Math0.Statements.A091817

/-! ### The primes -/

/-- The first prime among `q, q + 1, …, q + fuel - 1`, or `0` if there is none. -/
def firstPrimeFrom : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, q => if q.Prime then q else firstPrimeFrom fuel (q + 1)

/-- The least prime `> m`, searched in `m + 1, …, 2 m + 2` (Bertrand's postulate guarantees one,
see `primeAt_eq_nth`). -/
def nextPrime (m : ℕ) : ℕ := firstPrimeFrom (m + 2) (m + 1)

/-- The `i`-th prime, 0-indexed: `primeAt 0 = 2`, `primeAt 1 = 3`, … -/
def primeAt : ℕ → ℕ
  | 0 => 2
  | i + 1 => nextPrime (primeAt i)

theorem firstPrimeFrom_spec (fuel q : ℕ) (h : ∃ r, r.Prime ∧ q ≤ r ∧ r < q + fuel) :
    (firstPrimeFrom fuel q).Prime ∧ q ≤ firstPrimeFrom fuel q ∧
      ∀ r, q ≤ r → r < firstPrimeFrom fuel q → ¬ r.Prime := by
  induction fuel generalizing q with
  | zero => obtain ⟨r, -, h1, h2⟩ := h; omega
  | succ fuel ih =>
    rw [firstPrimeFrom]
    split_ifs with hq
    · exact ⟨hq, le_rfl, fun r h1 h2 => by omega⟩
    · obtain ⟨r, hr, h1, h2⟩ := h
      have hqr : q ≠ r := fun e => hq (e ▸ hr)
      obtain ⟨h1', h2', h3'⟩ := ih (q + 1) ⟨r, hr, by omega, by omega⟩
      refine ⟨h1', by omega, fun r' hr1 hr2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hr1 with e | e
      · exact e ▸ hq
      · exact h3' r' e hr2

/-- `primeAt` is Mathlib's `Nat.nth Nat.Prime`. -/
theorem primeAt_eq_nth (i : ℕ) : primeAt i = Nat.nth Nat.Prime i := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  induction i with
  | zero => simp [primeAt]
  | succ i ih =>
    rw [primeAt, ih]
    set m := Nat.nth Nat.Prime i with hm
    have hmp : m.Prime := Nat.nth_mem_of_infinite hinf i
    obtain ⟨r, hr, hr1, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul m hmp.ne_zero
    obtain ⟨hx, hx1, hx2⟩ :=
      firstPrimeFrom_spec (m + 2) (m + 1) ⟨r, hr, by omega, by omega⟩
    have hn : (Nat.nth Nat.Prime (i + 1)).Prime := Nat.nth_mem_of_infinite hinf (i + 1)
    have hlt : m < Nat.nth Nat.Prime (i + 1) := Nat.nth_strictMono hinf (Nat.lt_succ_self i)
    rw [nextPrime]
    rcases lt_trichotomy (firstPrimeFrom (m + 2) (m + 1)) (Nat.nth Nat.Prime (i + 1))
      with h | h | h
    · have := Nat.le_nth_of_lt_nth_succ h hx
      omega
    · exact h
    · exact absurd hn (hx2 _ (by omega) h)

/-! ### Harmonic numbers and the sequence -/

/-- The harmonic number `H m = 1 + 1/2 + ⋯ + 1/m` (`H 0 = 0`). -/
def H (m : ℕ) : ℚ := ((List.range m).map (fun k => (1 : ℚ) / ((k : ℚ) + 1))).sum

/-- The quantity attached to a prime `p`:
`(2*numerator(H(p-3)) - 3*denominator(H(p-3)))/p`, computed exactly in `ℚ`. -/
def term (p : ℕ) : ℚ := (2 * (H (p - 3)).num - 3 * ((H (p - 3)).den : ℤ) : ℚ) / (p : ℚ)

/-- A091817 (offset 1): `a(n) = (2*numerator(H(p-3)) - 3*denominator(H(p-3)))/p` where
`p = 3, 5, 7, 11, …` is the `(n+1)`-th prime (`primeAt n`, 0-indexed), as a rational number. -/
def a (n : ℕ) : ℚ := term (primeAt n)

/-- The first indices: `a 1, a 2, a 3, a 4` belong to `p = 3, 5, 7, 11`. -/
example : (List.range 4).map (fun i => primeAt (i + 1)) = [3, 5, 7, 11] := by decide +kernel

/-- The definition reproduces all 18 terms listed in OEIS, `a 1, …, a 18`
(`p = 3, …, 67`; kernel-checked). -/
theorem a_data : (List.range 18).map (fun i => a (i + 1)) =
    [-1, 0, 2, 62, 554, 74258, 142682, 2830946, 1448977246, 12576415426, 1857881203154,
      64634117421826, 62771945063582, 164497840779865642, 350742295126606034006,
      5774653629556529218142, 5647762835059481932498, 12720214895833193424471634] := by
  decide +kernel

/-- Conjecture (Leroy Quet): the terms are always integral, i.e. for every `n ≥ 1` the rational
number `a n = (2*numerator(H(p-3)) - 3*denominator(H(p-3)))/p` (with `p` the `(n+1)`-th prime)
is an integer. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, a n = (z : ℚ)

end Math0.Statements.A091817
