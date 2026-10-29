/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A005590
import Math0.Audit

/-!
# Zeros of `a(3n)` for the signed Stern sequence A005590 are the fibbinary numbers

We prove Ralf Stephan's conjecture: `a(3n) = 0 ↔ n` is fibbinary (no two adjacent 1 bits).

**Automaton.** Put `v(m) = (a(m), a(m+1))`. Then `v(2m) = (x, y - x)` and
`v(2m+1) = (y - x, y)` where `(x, y) = v(m)`. Reading the bits of `m` from the most significant
one, starting at `v(0) = (0, 1)`, define a three-state automaton `st`:
state `0` (`v = (0,1)`), state `1` (`v = (1,1)`), state `2` (an absorbing "dead" state).
Transitions: bit `0` maps `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 2`; bit `1` maps `0 ↦ 1`, `1 ↦ 0`, `2 ↦ 2`.
In the dead state `v = (x, y)` satisfies `P(x,y) : (0 < x ∧ y < x) ∨ (x < 0 ∧ x < y)`; this is
preserved by both linear maps, `(1,0)` satisfies it, and it forces `x ≠ 0`. Hence
`a(m) = 0 ↔ st(m) = 0`.

**Multiples of three.** `3·(2k) = 2·(3k)`, `3·(4k+1) = 2·(2·(3k)+1)+1` and
`3·(4k+3) = 2·(2·(3k+2))+1`. So `st(6k) = 0 ↔ st(3k) = 0`, `st(12k+3) = 0 ↔ st(3k) = 0`, and
`st(12k+9) ≠ 0` always. The fibbinary property satisfies the same recursion:
`fib(2k) ↔ fib(k)`, `fib(4k+1) ↔ fib(k)`, `¬ fib(4k+3)`. Strong induction finishes.
-/

namespace Math0.Frontier.A005590
open Math0.Statements.A005590

/-- The automaton state of `m`, read from the most significant bit (values `0`, `1`, `2`). -/
private def st : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then (if st ((n + 1) / 2) = 0 then 0 else 2)
    else (if st ((n + 1) / 2) = 0 then 1 else if st ((n + 1) / 2) = 1 then 0 else 2)
  decreasing_by all_goals omega

/-- `st 0 = 0`. -/
private lemma st_zero : st 0 = 0 := by rw [st]

/-- Transition on bit `0`. -/
private lemma st_even (k : ℕ) : st (2 * k) = if st k = 0 then 0 else 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [st_zero]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [e, st]
    have h1 : (2 * j + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [if_pos h1, h2]

/-- Transition on bit `1`. -/
private lemma st_odd (k : ℕ) :
    st (2 * k + 1) = if st k = 0 then 1 else if st k = 1 then 0 else 2 := by
  rw [st]
  have h1 : ¬ (2 * k + 1) % 2 = 0 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [if_neg h1, h2]

/-- The invariant linking the automaton state of `m` with `(a m, a (m+1))`. -/
private def Inv (m : ℕ) : Prop :=
  (st m = 0 ∧ a m = 0 ∧ a (m + 1) = 1) ∨ (st m = 1 ∧ a m = 1 ∧ a (m + 1) = 1) ∨
    (st m = 2 ∧ ((0 < a m ∧ a (m + 1) < a m) ∨ (a m < 0 ∧ a m < a (m + 1))))

/-- The invariant holds for every `m`. -/
private lemma inv_all (m : ℕ) : Inv m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · left
        exact ⟨st_zero, a_zero, a_one⟩
      · have IH := ih k (by omega)
        unfold Inv at IH ⊢
        rw [st_even, a_even, a_odd]
        rcases IH with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1⟩
        · left; rw [h0, h1, h2]; simp
        · right; right; rw [h0, h1, h2]; simp
        · right; right; rw [h0]; simp; omega
    · have IH := ih k (by omega)
      unfold Inv at IH ⊢
      have e : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      rw [st_odd, a_odd, e, a_even]
      rcases IH with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1⟩
      · right; left; rw [h0, h1, h2]; simp
      · left; rw [h0, h1, h2]; simp
      · right; right; rw [h0]; simp; omega

/-- `a m = 0` exactly when the automaton is in state `0`. -/
private lemma a_eq_zero_iff (m : ℕ) : a m = 0 ↔ st m = 0 := by
  rcases inv_all m with ⟨h0, h1, _⟩ | ⟨h0, h1, _⟩ | ⟨h0, h1⟩
  · simp [h0, h1]
  · simp [h0, h1]
  · rw [h0]; constructor
    · intro h; omega
    · intro h; omega

/-- The state is always at most `2`. -/
private lemma st_le (m : ℕ) : st m ≤ 2 := by
  rcases inv_all m with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ <;> omega

/-- One step of the fibbinary recursion: look at the two lowest bits, then drop one bit. -/
private lemma fib_iff (n : ℕ) :
    IsFibbinary n ↔ ¬ (n % 2 = 1 ∧ (n / 2) % 2 = 1) ∧ IsFibbinary (n / 2) := by
  unfold IsFibbinary
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro ⟨h1, h2⟩
      apply h 0
      rw [Nat.testBit_zero, Nat.testBit_succ, Nat.testBit_zero]
      simp [h1, h2]
    · intro i
      rw [← Nat.testBit_succ, ← Nat.testBit_succ]
      exact h (i + 1)
  · intro ⟨h1, h2⟩ i
    cases i with
    | zero =>
      rw [Nat.testBit_zero, Nat.testBit_succ, Nat.testBit_zero]
      simp only [decide_eq_true_eq]
      exact h1
    | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ]
      exact h2 i

/-- `0` is fibbinary. -/
private lemma fib_zero : IsFibbinary 0 := by
  intro i; simp

/-- The state of `3n` is `0` exactly when `n` is fibbinary. -/
private lemma st_three_mul (n : ℕ) : st (3 * n) = 0 ↔ IsFibbinary n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [st_zero, fib_zero]
    · have hmod : n % 2 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3 := by omega
      rcases hmod with h | h | h
      · -- n = 2k
        obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
        have e : 3 * (2 * k) = 2 * (3 * k) := by ring
        have h3 : (2 * k) / 2 = k := by omega
        rw [e, st_even, fib_iff, h3, ← ih k (by omega)]
        constructor
        · intro hs
          refine ⟨by omega, ?_⟩
          by_contra hc; rw [if_neg hc] at hs; omega
        · intro ⟨_, hs⟩; rw [if_pos hs]
      · -- n = 4k + 1
        obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 1 := ⟨n / 4, by omega⟩
        have e : 3 * (4 * k + 1) = 2 * (2 * (3 * k) + 1) + 1 := by ring
        have h3 : (4 * k + 1) / 2 / 2 = k := by omega
        rw [e, st_odd, st_odd, fib_iff, fib_iff (_ / 2), h3, ← ih k (by omega)]
        have hl := st_le (3 * k)
        have h4 : (4 * k + 1) / 2 % 2 = 0 := by omega
        rw [h4]
        rcases (show st (3 * k) = 0 ∨ st (3 * k) = 1 ∨ st (3 * k) = 2 by omega) with
          hs | hs | hs <;> simp [hs]
      · -- n = 4k + 3
        obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
        have e : 3 * (4 * k + 3) = 2 * (2 * (3 * k + 2)) + 1 := by ring
        rw [e, st_odd, st_even, fib_iff]
        have h3 : (4 * k + 3) % 2 = 1 := by omega
        have h4 : (4 * k + 3) / 2 % 2 = 1 := by omega
        rw [h3, h4]
        rcases (show st (3 * k + 2) = 0 ∨ st (3 * k + 2) ≠ 0 by omega) with hs | hs <;>
          simp [hs]

/-- Stephan's conjecture: `a(3n) = 0` iff `n` is fibbinary. -/
theorem result : statement := by
  intro n
  rw [a_eq_zero_iff, st_three_mul]

end Math0.Frontier.A005590

#math0_settles Math0.Frontier.A005590.result Math0.Statements.A005590.statement
