/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A335012: distinct remainders of the repunits 1, 11, ..., R_n modulo n

Source: https://oeis.org/A335012, _Sen-Peng Eu_, May 19 2020. Verbatim:
> Conjecture: a(n) = n-1 if and only if n is a long period prime (A006883), that is, n is a prime
> and the decimal expansion of 1/n has period n-1.

The entry's definition: "Number of different remainders when the first n terms of
1, 11, 111, 1111, ... are divided by n." (offset `1`).

## Encoding

* The `k`-th term of `1, 11, 111, ...` is the repunit `R_k = (10^k - 1) / 9` (`k ≥ 1`), and
  `a n` is the number of distinct values `R_k % n` for `1 ≤ k ≤ n`, i.e. the cardinality of the
  image of `k ↦ R_k % n` on `Finset.Icc 1 n`. This is exactly the PARI/Maple programs of the
  entry. `a_data` checks all 81 listed terms `a(1..81)`.
* A006883 ("Long period primes: the decimal expansion of 1/p has period p-1") includes `2`, by the
  convention stated there (1/2 = 0.5000..., period 1 = 2-1); its own Maple/Mathematica programs
  test `p = 2 ∨ ord_p(10) = p - 1` over primes `p`. For a prime `p ∉ {2, 5}` the period of the
  decimal expansion of `1/p` is the multiplicative order of `10` modulo `p`; for `p = 5` the
  period is `1 ≠ 4` (and `orderOf (10 : ZMod 5) = orderOf 0 = 0 ≠ 4` in Mathlib, so no special
  case is needed there). Hence `IsLongPeriodPrime p := p.Prime ∧ (p = 2 ∨ orderOf (10 : ZMod p) =
  p - 1)`. As a sanity check, `isLongPeriodPrime_data` (kernel-checked, through the decidable
  reformulation `isLongPeriodPrimeB_iff`) reproduces the first 24 listed terms of A006883 (the
  members below 270).
* The conjecture is read for every index of the sequence, i.e. all `n ≥ 1` (offset 1). (For
  `n = 0` the truncated subtraction would make `a 0 = 0 - 1` hold vacuously, so the range
  `1 ≤ n` is part of the statement.)
-/

namespace Math0.Statements.A335012

/-- A335012: the number of different remainders when the first `n` repunits
`1, 11, 111, ..., R_n` (with `R_k = (10^k - 1) / 9`) are divided by `n`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).image (fun k => ((10 ^ k - 1) / 9) % n)).card

/-- The definition reproduces the 81 terms `a(1), ..., a(81)` listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 81).map (fun i => a (i + 1)) =
    [1, 1, 3, 2, 1, 3, 6, 3, 9, 1, 2, 4, 6, 6, 3, 4, 16, 9, 18, 2, 6, 2, 22, 5, 2, 6, 27, 7, 28, 3,
      15, 5, 6, 16, 6, 10, 3, 18, 6, 3, 5, 6, 21, 3, 9, 22, 46, 6, 42, 2, 48, 7, 13, 27, 2, 8, 18,
      28, 58, 4, 60, 15, 18, 6, 6, 6, 33, 17, 66, 6, 35, 11, 8, 3, 4, 19, 6, 6, 13, 4, 81] := by
  decide +kernel

/-- Long period primes (A006883): primes `p` such that the decimal expansion of `1/p` has period
`p - 1`. For `p = 2` the period is `1 = p - 1` (A006883 includes `2`); for every other prime the
condition is that `10` has multiplicative order `p - 1` modulo `p` (for `p = 5`, where `10 ≡ 0`,
Mathlib's `orderOf` is `0`, matching the fact that `1/5` has period `1 ≠ 4`). -/
def IsLongPeriodPrime (p : ℕ) : Prop :=
  p.Prime ∧ (p = 2 ∨ orderOf (10 : ZMod p) = p - 1)

/-- A decidable reformulation of `IsLongPeriodPrime`, used only for the sanity check below. -/
def isLongPeriodPrimeB (p : ℕ) : Bool :=
  decide p.Prime && (p == 2 || (10 ^ (p - 1) % p == 1 % p &&
    (List.range' 1 (p - 2)).all fun m => 10 ^ m % p != 1 % p))

theorem isLongPeriodPrimeB_iff (p : ℕ) : isLongPeriodPrimeB p = true ↔ IsLongPeriodPrime p := by
  have key : ∀ m : ℕ, (10 : ZMod p) ^ m = 1 ↔ 10 ^ m % p = 1 % p := fun m => by
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rfl
  simp only [isLongPeriodPrimeB, IsLongPeriodPrime, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range'_1, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · right
      have h2' := hp.two_le
      rw [orderOf_eq_iff (by omega)]
      refine ⟨(key _).2 h1, fun m hm hm0 => ?_⟩
      rw [Ne, key]
      exact h2 m ⟨hm0, by omega⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      have h2' := hp.two_le
      rw [orderOf_eq_iff (by omega)] at h
      refine ⟨(key _).1 h.1, fun m hm => ?_⟩
      rw [← key]
      exact h.2 m (by omega) hm.1

/-- Sanity check: the long period primes below `270` are exactly the first 24 terms of A006883
listed in OEIS (kernel-checked). -/
theorem isLongPeriodPrime_data :
    (List.range 270).filter isLongPeriodPrimeB =
      [2, 7, 17, 19, 23, 29, 47, 59, 61, 97, 109, 113, 131, 149, 167, 179, 181, 193, 223, 229,
        233, 257, 263, 269] := by
  decide +kernel

/-- Conjecture (Eu, A335012): for every `n ≥ 1`, `a(n) = n - 1` if and only if `n` is a long
period prime (A006883), i.e. `n` is prime and the decimal expansion of `1/n` has period `n - 1`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n = n - 1 ↔ IsLongPeriodPrime n)

end Math0.Statements.A335012
