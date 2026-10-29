/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A097154
import Math0.Audit

/-!
# The only fixed points of `reverse(x) - maxdigit(x)` are `0` and `89`

We prove Earls' conjecture from A097154: `f x = x` iff `x = 0` or `x = 89`.

Idea. `f x = x` means `rev x = x + c` with `c = maxDigit x ≤ 9`. Reversal keeps the digit sum,
so `rev x ≡ x (mod 9)` and `9 ∣ c`. If `x ≠ 0` its leading digit is nonzero, so `c = 9`.
A one-digit `x` has `rev x = x`, impossible. Otherwise write the little-endian digit list as
`b :: (M ++ [a])` (`b` the units digit, `a` the leading digit, `M` the middle block), with
`m`, `r` the values of `M` and of its reversal and `P = 10 ^ |M|`. Then
`x = b + 10 m + 10 P a` and `rev x = a + 10 r + 10 P b`. Mod `10`, `a ≡ b - 1`, so either
`b = a + 1` or `a = 9, b = 0`. The second case gives `r = m + 9P ≥ P`, impossible. The first
gives `r + P = m + 1`, so `r = 0` (as `m < P`); then all middle digits vanish, `m = 0` and
`P = 1`, i.e. `M = []`. Hence `x = 10 a + (a + 1)` and its largest digit `a + 1` is `9`,
so `x = 89`.
-/

namespace Math0.Frontier.A097154
open Math0.Statements.A097154

/-- Every element of a list is at most its `foldr max 0`. -/
private theorem le_foldr_max : ∀ (l : List ℕ) (d : ℕ), d ∈ l → d ≤ l.foldr max 0
  | [], d, h => by simp at h
  | e :: l, d, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max l d h) (le_max_right _ _)

/-- A digit list made of zeros has value `0`. -/
private theorem ofDigits_eq_zero : ∀ L : List ℕ, (∀ d ∈ L, d = 0) → Nat.ofDigits 10 L = 0
  | [], _ => rfl
  | e :: L, h => by
    rw [Nat.ofDigits_cons, h e List.mem_cons_self,
      ofDigits_eq_zero L (fun d hd => h d (List.mem_cons_of_mem e hd))]

/-- Reversing a digit list does not change its value mod `9`. -/
private theorem ofDigits_reverse_mod (L : List ℕ) :
    Nat.ofDigits 10 L.reverse % 9 = Nat.ofDigits 10 L % 9 := by
  have h1 := Nat.ofDigits_modEq 10 9 L
  have h2 := Nat.ofDigits_modEq 10 9 L.reverse
  norm_num [Nat.ofDigits_one, List.sum_reverse] at h1 h2
  exact h2.trans h1.symm

/-- The core: a nonempty digit list with nonzero leading digit whose reversal exceeds it by its
largest digit is `[9, 8]` (the number `89`). -/
private theorem key (L : List ℕ) (hL : ∀ d ∈ L, d < 10) (hlast : ∀ h : L ≠ [], L.getLast h ≠ 0)
    (heq : Nat.ofDigits 10 L.reverse = Nat.ofDigits 10 L + L.foldr max 0) (hne : L ≠ []) :
    L = [9, 8] := by
  have hmod := ofDigits_reverse_mod L
  have hc9 : L.foldr max 0 ≤ 9 := foldr_max_le L 9 fun d hd => by have := hL d hd; omega
  rcases L with _ | ⟨b, T⟩
  · exact absurd rfl hne
  rcases List.eq_nil_or_concat' T with rfl | ⟨M, a, rfl⟩
  · -- one digit: `rev x = x`
    have hb := le_foldr_max [b] b List.mem_cons_self
    have hb0 := hlast (by simp)
    simp only [List.reverse_singleton, List.getLast_singleton] at heq hb0
    omega
  · set c := (b :: (M ++ [a])).foldr max 0
    have ha : a ≤ c := le_foldr_max _ a (by simp)
    have hb : b ≤ c := le_foldr_max _ b (by simp)
    have ha0 : a ≠ 0 := by
      have := hlast (by simp)
      simpa using this
    have ha9 : a < 10 := hL a (by simp)
    have hb9 : b < 10 := hL b (by simp)
    have hx : Nat.ofDigits 10 (b :: (M ++ [a])) =
        b + 10 * Nat.ofDigits 10 M + 10 * (10 ^ M.length * a) := by
      simp only [Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_nil]
      ring
    have hrx : Nat.ofDigits 10 (b :: (M ++ [a])).reverse =
        a + 10 * Nat.ofDigits 10 M.reverse + 10 * (10 ^ M.length * b) := by
      simp only [List.reverse_cons, List.reverse_append, List.reverse_nil, List.nil_append,
        List.singleton_append, Nat.ofDigits_append, Nat.ofDigits_cons, Nat.ofDigits_nil,
        List.length_cons, List.length_reverse, pow_succ]
      ring
    have hmP : Nat.ofDigits 10 M < 10 ^ M.length := Nat.ofDigits_lt_base_pow_length (by norm_num)
      fun d hd => hL d (by simp [hd])
    have hrP : Nat.ofDigits 10 M.reverse < 10 ^ M.length := by
      have := Nat.ofDigits_lt_base_pow_length (b := 10) (l := M.reverse) (by norm_num)
        fun d hd => hL d (by simp [List.mem_reverse.1 hd])
      simpa using this
    have hP1 : 1 ≤ 10 ^ M.length := Nat.one_le_pow _ _ (by norm_num)
    have hzero : Nat.ofDigits 10 M.reverse = 0 → Nat.ofDigits 10 M = 0 := fun h0 =>
      ofDigits_eq_zero M fun d hd => by
        have := le_ofDigits_of_mem M.reverse d (List.mem_reverse.2 hd)
        omega
    have hlen : 1 ≤ M.length → 10 ≤ 10 ^ M.length := fun h1 =>
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h1)
    generalize Nat.ofDigits 10 M = m at hx hmP hzero
    generalize Nat.ofDigits 10 M.reverse = r at hrx hrP hzero
    generalize hP : 10 ^ M.length = P at hx hrx hmP hrP hP1 hlen
    rw [hx, hrx] at heq hmod
    have hc' : c = 9 := by omega
    have hab : b = a + 1 ∨ (a = 9 ∧ b = 0) := by omega
    rcases hab with rfl | ⟨rfl, rfl⟩
    · have e1 : P * (a + 1) = P * a + P := by ring
      have hr0 : r = 0 := by omega
      have hm0 : m = 0 := hzero hr0
      have hlen0 : M.length = 0 := by omega
      have hMnil : M = [] := List.length_eq_zero_iff.1 hlen0
      subst hMnil
      have hcle : c ≤ a + 1 := foldr_max_le _ _ fun d hd => by
        simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hd
        omega
      have : a = 8 := by omega
      subst this
      rfl
    · simp at heq
      omega

/-- Earls' conjecture (A097154): `0` and `89` are the only fixed points of
`f(x) = reverse(x) - maxdigit(x)`. -/
theorem result : statement := by
  intro x
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      have hrev : rev x = x + maxDigit x := by
        have := maxDigit_le_rev x
        unfold f at h
        omega
      have hL := key (Nat.digits 10 x) (fun d hd => Nat.digits_lt_base (by norm_num) hd)
        (fun _ => Nat.getLast_digit_ne_zero 10 hx)
        (by rw [Nat.ofDigits_digits]; exact hrev) (Nat.digits_ne_nil_iff_ne_zero.mpr hx)
      have := Nat.ofDigits_digits 10 x
      rw [hL, show Nat.ofDigits 10 [9, 8] = 89 by decide] at this
      exact this.symm
  · rintro (rfl | rfl)
    · exact f_examples.2.2.2.2.1
    · exact f_examples.2.2.2.2.2.2.2

end Math0.Frontier.A097154

#math0_settles Math0.Frontier.A097154.result Math0.Statements.A097154.statement
