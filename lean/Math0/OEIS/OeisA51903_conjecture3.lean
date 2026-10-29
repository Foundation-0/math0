/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.OEIS.«51903»
import Math0.Audit

/-!
# An odd $n$ with $a(n) > 1$ and $2^n \equiv 2^{a(n)} \pmod n$

Thomas Ordowski (OEIS A051903, Dec 2019) asked whether there are odd numbers $n$ whose maximal
prime exponent $a(n)$ exceeds $1$ and which satisfy $2^n \equiv 2^{a(n)} \pmod n$. We answer
`OeisA51903.conjecture3` positively with the explicit witness
$n = 9687963167864344937 = 7 \cdot 631 \cdot 881 \cdot 3511^2 \cdot 201961$, for which $a(n) = 2$
and $2^n \equiv 4 \pmod n$. The factorization is certified by Mathlib's
`Nat.primeFactorsList` simproc, and the congruence by fast modular exponentiation in
`ZMod n` (`reduce_mod_char`). Conceptually, $3511$ is a Wieferich prime with
$\operatorname{ord}_{3511^2}(2) = 1755$, and the multiplicative orders of $2$ modulo the other prime
factors all divide $19305 = 11 \cdot 1755$, which divides $n - 2$.
-/

namespace Math0.OeisA51903

/-- The prime factorization of the witness: `N = 7 * 631 * 881 * 3511 ^ 2 * 201961`. -/
theorem primeFactorsList_N :
    Nat.primeFactorsList 9687963167864344937 = [7, 631, 881, 3511, 3511, 201961] := by
  simp only [Nat.primeFactorsList_ofNat]

/-- The maximal exponent in the prime factorization of the witness is `2`. -/
theorem a_N : OeisA51903.a 9687963167864344937 = 2 := by
  rw [OeisA51903.a, primeFactorsList_N]
  decide

/-- `2 ^ N = 4` in `ZMod N`, by fast modular exponentiation. -/
theorem two_pow_N_zmod : (2 : ZMod 9687963167864344937) ^ 9687963167864344937 = 4 := by
  reduce_mod_char

/-- `2 ^ N ≡ 2 ^ 2 [MOD N]`. -/
theorem two_pow_N_modEq : 2 ^ 9687963167864344937 ≡ 2 ^ 2 [MOD 9687963167864344937] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, two_pow_N_zmod]
  rfl

/-- There is an odd `n` with `a n > 1` and `2 ^ n ≡ 2 ^ (a n) [MOD n]`, namely
`n = 7 * 631 * 881 * 3511 ^ 2 * 201961`. -/
theorem conjecture3 : type_of% @OeisA51903.conjecture3 := by
  refine ⟨9687963167864344937, ⟨4843981583932172468, by norm_num⟩, ?_, ?_⟩
  · rw [a_N]; decide
  · rw [a_N]; exact two_pow_N_modEq

end Math0.OeisA51903

#math0_proves Math0.OeisA51903.conjecture3 OeisA51903.conjecture3
