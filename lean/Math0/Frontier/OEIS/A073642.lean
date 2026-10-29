/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A073642
import Math0.Audit

/-!
# Yanev's identity for A073642 (sum of the positions of the 1-bits)

We prove Velin Yanev's conjecture: for every `n > 0`,
`a(n) = (3 * A011371(n) - ∑_{k=1}^{n} A007814(k)^2) / 2`, where `a(n)` is the sum of the
positions of the 1-bits of `n`, `A011371(n) = v₂(n!)` and `A007814(k) = v₂(k)`.

**Idea.** Write `v = v₂(n+1)`. Since `v₂((n+1)!) = v₂(n!) + v` and the sum of squares gains
`v²`, the identity `2 a(n) + ∑_{k ≤ n} v₂(k)² = 3 v₂(n!)` (true at `n = 0`) follows by induction
from the local identity `2 a(n+1) + v² = 2 a(n) + 3 v`. That identity, together with the
popcount identity `s(n+1) + v = s(n) + 1` (`s` = number of 1-bits), is proved by strong
induction on `n` using `a(2k) = a(2k+1) = a(k) + s(k)`, `s(2k) = s(k)`, `s(2k+1) = s(k) + 1`,
`v₂(2k+1) = 0` and `v₂(2k) = v₂(k) + 1`.
-/

namespace Math0.Frontier.A073642
open Math0.Statements.A073642

/-- The number of 1-bits of `n` (the binary weight). -/
private def L (n : ℕ) : ℕ := (Nat.bitIndices n).length

/-- `a(2k) = a(k) + s(k)`. -/
private lemma a_two_mul (k : ℕ) : a (2 * k) = a k + L k := by
  simp [a, L]

/-- `a(2k+1) = a(k) + s(k)`. -/
private lemma a_two_mul_add_one (k : ℕ) : a (2 * k + 1) = a k + L k := by
  simp [a, L]

/-- `s(2k) = s(k)`. -/
private lemma L_two_mul (k : ℕ) : L (2 * k) = L k := by simp [L]

/-- `s(2k+1) = s(k) + 1`. -/
private lemma L_two_mul_add_one (k : ℕ) : L (2 * k + 1) = L k + 1 := by simp [L]

/-- `v₂(2k) = v₂(k) + 1` for `k ≠ 0`. -/
private lemma v2_two_mul {k : ℕ} (hk : k ≠ 0) :
    padicValNat 2 (2 * k) = padicValNat 2 k + 1 := by
  rw [padicValNat.mul (by norm_num) hk, padicValNat.self (by norm_num)]; ring

/-- `v₂(2k+1) = 0`. -/
private lemma v2_odd (k : ℕ) : padicValNat 2 (2 * k + 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

/-- Popcount identity: `s(n+1) + v₂(n+1) = s(n) + 1`. -/
private lemma L_succ (n : ℕ) : L (n + 1) + padicValNat 2 (n + 1) = L n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [L_two_mul_add_one, L_two_mul, v2_odd]
    · have h := ih k (by omega)
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, L_two_mul, v2_two_mul (by omega),
        L_two_mul_add_one]
      omega

/-- Local identity: `2 a(n+1) + v₂(n+1)² = 2 a(n) + 3 v₂(n+1)`. -/
private lemma key (n : ℕ) :
    2 * a (n + 1) + padicValNat 2 (n + 1) ^ 2 = 2 * a n + 3 * padicValNat 2 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [a_two_mul_add_one, a_two_mul, v2_odd]; ring
    · have h := ih k (by omega)
      have hL := L_succ k
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, a_two_mul, v2_two_mul (by omega),
        a_two_mul_add_one]
      nlinarith

/-- The identity in `ℕ`: `2 a(n) + ∑_{k=1}^{n} v₂(k)² = 3 v₂(n!)`. -/
private lemma main (n : ℕ) :
    2 * a n + ∑ k ∈ Finset.Icc 1 n, padicValNat 2 k ^ 2 = 3 * padicValNat 2 n.factorial := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero n)]
    have := key n
    linarith

/-- Yanev's conjecture holds: for every `n > 0`,
`a(n) = (3 * A011371(n) - ∑_{k=1}^{n} A007814(k)^2) / 2`. -/
theorem result : statement := by
  intro n _
  have h := main n
  have h' : (2 * (a n : ℚ) + ∑ k ∈ Finset.Icc 1 n, ((padicValNat 2 k : ℕ) : ℚ) ^ 2) =
      3 * (padicValNat 2 n.factorial : ℚ) := by exact_mod_cast h
  rw [eq_div_iff (by norm_num : (2:ℚ) ≠ 0), A011371_eq_padicValNat_factorial]
  simp only [A007814]
  linarith

end Math0.Frontier.A073642

#math0_settles Math0.Frontier.A073642.result Math0.Statements.A073642.statement
