/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A005590: zeros of `a(3n)` for the signed Stern sequence are the fibbinary numbers

Source: https://oeis.org/A005590, Ralf Stephan, May 02 2003 (FORMULA section). Verbatim:
> Conjecture: a(3n)=0 iff n in A003714.

The sequence (offset `0`) is "a(0) = 0, a(1) = 1, a(2n) = a(n), a(2n+1) = a(n+1) - a(n)."
A003714 is the sequence of fibbinary numbers, "numbers whose binary representation contains
no two adjacent 1's" (`0, 1, 2, 4, 5, 8, 9, 10, 16, …`).

## Encoding

* The values are signed, so `a : ℕ → ℤ`. It is computed by the defining recursion with a fuel
  argument (`aux`), so that the kernel can evaluate it. With fuel `n + 1` the recursion is never
  cut off: every recursive call is on a strictly smaller argument (`n / 2 < n` for even `n ≥ 2`,
  `n / 2 + 1 < n` for odd `n ≥ 3`). The theorems `a_zero`, `a_one`, `a_even`, `a_odd` prove that
  `a` satisfies exactly the OEIS defining equations, for every `n`, and these equations
  determine the sequence. `a_data` checks all 105 listed terms `a 0, …, a 104`.
* "n in A003714" is `IsFibbinary n`: no two adjacent bits of `n` are both `1`, i.e. there is no
  `i` with `Nat.testBit n i` and `Nat.testBit n (i + 1)` both true (bits beyond the length of the
  binary representation are `0`, so this is a statement about the binary representation of
  `n`). `isFibbinary_iff_land` shows it is equivalent to `n &&& (n >>> 1) = 0`, which makes it
  decidable, and `fibbinary_data` checks that it picks out exactly the 61 terms listed in
  A003714 (all fibbinary numbers up to `264`).
* The conjecture is stated for every `n ≥ 0` (both sequences start at offset `0`; `a 0 = 0` and
  `0` is in A003714): `a (3 * n) = 0 ↔ IsFibbinary n`.
-/

namespace Math0.Statements.A005590

/-- The defining recursion of A005590 run with `fuel` steps (it returns `0` when the fuel is
exhausted, which never happens for `fuel > n`; see `aux_eq_aux`). -/
def aux : ℕ → ℕ → ℤ
  | 0, _ => 0
  | fuel + 1, n =>
    if n ≤ 1 then (n : ℤ)
    else if n % 2 = 0 then aux fuel (n / 2)
    else aux fuel (n / 2 + 1) - aux fuel (n / 2)

/-- A005590: `a(0) = 0`, `a(1) = 1`, `a(2n) = a(n)`, `a(2n+1) = a(n+1) - a(n)`. -/
def a (n : ℕ) : ℤ := aux (n + 1) n

/-- The fueled recursion does not depend on the fuel once the fuel exceeds the argument. -/
theorem aux_eq_aux : ∀ (f g n : ℕ), n < f → n < g → aux f n = aux g n := by
  intro f
  induction f with
  | zero => intro g n hf; omega
  | succ f ih =>
    intro g n hf hg
    cases g with
    | zero => omega
    | succ g =>
      simp only [aux]
      split_ifs with h1 h2
      · rfl
      · exact ih g (n / 2) (by omega) (by omega)
      · rw [ih g (n / 2 + 1) (by omega) (by omega), ih g (n / 2) (by omega) (by omega)]

theorem aux_succ (fuel n : ℕ) : aux (fuel + 1) n =
    if n ≤ 1 then (n : ℤ)
    else if n % 2 = 0 then aux fuel (n / 2)
    else aux fuel (n / 2 + 1) - aux fuel (n / 2) := rfl

theorem aux_eq_a (f n : ℕ) (h : n < f) : aux f n = a n :=
  aux_eq_aux f (n + 1) n h (by omega)

theorem a_zero : a 0 = 0 := by decide +kernel

theorem a_one : a 1 = 1 := by decide +kernel

/-- `a(2n) = a(n)` for all `n`. -/
theorem a_even (n : ℕ) : a (2 * n) = a n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · show aux (2 * n + 1) (2 * n) = a n
    rw [aux_succ, if_neg (by omega), if_pos (by omega), Nat.mul_div_cancel_left n (by omega)]
    exact aux_eq_a _ _ (by omega)

/-- `a(2n+1) = a(n+1) - a(n)` for all `n`. -/
theorem a_odd (n : ℕ) : a (2 * n + 1) = a (n + 1) - a n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide +kernel
  · show aux (2 * n + 1 + 1) (2 * n + 1) = a (n + 1) - a n
    have h : (2 * n + 1) / 2 = n := by omega
    rw [aux_succ, if_neg (by omega), if_neg (by omega), h, aux_eq_a _ _ (by omega),
      aux_eq_a _ _ (by omega)]

/-- The definition reproduces all 105 terms listed in OEIS, `a 0, …, a 104` (kernel-checked). -/
theorem a_data : (List.range 105).map (fun i => a (i + 0)) =
    [0, 1, 1, 0, 1, -1, 0, 1, 1, -2, -1, 1, 0, 1, 1, 0, 1, -3, -2, 1, -1, 2, 1, -1, 0, 1, 1, 0,
      1, -1, 0, 1, 1, -4, -3, 1, -2, 3, 1, -2, -1, 3, 2, -1, 1, -2, -1, 1, 0, 1, 1, 0, 1, -1, 0,
      1, 1, -2, -1, 1, 0, 1, 1, 0, 1, -5, -4, 1, -3, 4, 1, -3, -2, 5, 3, -2, 1, -3, -2, 1, -1, 4,
      3, -1, 2, -3, -1, 2, 1, -3, -2, 1, -1, 2, 1, -1, 0, 1, 1, 0, 1, -1, 0, 1, 1] := by
  decide +kernel

/-- `n` is a fibbinary number (OEIS A003714): its binary representation contains no two
adjacent 1's. -/
def IsFibbinary (n : ℕ) : Prop :=
  ∀ i : ℕ, ¬ (n.testBit i = true ∧ n.testBit (i + 1) = true)

/-- The usual bitwise test for fibbinary numbers: `n AND (n >> 1) = 0`. -/
theorem isFibbinary_iff_land (n : ℕ) : IsFibbinary n ↔ n &&& (n >>> 1) = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit]
    have := h i
    rw [Nat.add_comm 1 i]
    cases hi : n.testBit i <;> cases hi1 : n.testBit (i + 1) <;> simp_all
  · intro h i ⟨hi, hi1⟩
    have := congrArg (fun m => m.testBit i) h
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit] at this
    rw [Nat.add_comm 1 i, hi, hi1] at this
    simp at this

instance : DecidablePred IsFibbinary := fun n =>
  decidable_of_iff _ (isFibbinary_iff_land n).symm

/-- `IsFibbinary` picks out exactly the 61 terms listed in A003714 (kernel-checked). -/
theorem fibbinary_data : (List.range 265).filter (fun n => decide (IsFibbinary n)) =
    [0, 1, 2, 4, 5, 8, 9, 10, 16, 17, 18, 20, 21, 32, 33, 34, 36, 37, 40, 41, 42, 64, 65, 66, 68,
      69, 72, 73, 74, 80, 81, 82, 84, 85, 128, 129, 130, 132, 133, 136, 137, 138, 144, 145, 146,
      148, 149, 160, 161, 162, 164, 165, 168, 169, 170, 256, 257, 258, 260, 261, 264] := by
  decide +kernel

/-- Conjecture (Ralf Stephan, 2003): for every `n ≥ 0`, `a(3n) = 0` if and only if `n` is a
fibbinary number (in A003714), i.e. the binary representation of `n` has no two adjacent 1's. -/
def statement : Prop :=
  ∀ n : ℕ, a (3 * n) = 0 ↔ IsFibbinary n

end Math0.Statements.A005590
