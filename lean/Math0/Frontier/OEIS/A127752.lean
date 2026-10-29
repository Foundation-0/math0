/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A127752
import Math0.Audit

/-!
# A127752 mod 2 is the first Feigenbaum symbolic sequence A035263

We prove Paul Barry's conjecture `a(n) mod 2 = A035263(n+1)`.

**The recursion for `a`.** The defining forward substitution says that the sum of `a j` over
`⌈n/2⌉ ≤ j ≤ n` is `3n+1`. Comparing the windows for `n = 2m`, `2m+1` and `2m+2` gives
`a(2m+2) = 3` and `a(2m+1) = a(m) + 3`, while `a(0) = 1`. So `a(2m)` is odd and
`a(2m+1) ≡ a(m) + 1 (mod 2)`.

**The recursion for A035263.** The infinite word is a fixed point of `0 ↦ 11, 1 ↦ 10`, so its
letter at (0-based) position `2m` is `1` and its letter at position `2m+1` is `1` if the letter
at position `m` is `0` and `0` otherwise. With `c(m) = A035263(m+1)` this reads `c(2m) = 1`,
`c(2m+1) = 1 - c(m)`.

Both sequences satisfy the same recursion mod 2, so strong induction finishes.
-/

namespace Math0.Frontier.A127752
open Math0.Statements.A127752
open Finset

/-- The window identity: the sum of `a j` over `⌈n/2⌉ ≤ j ≤ n` is `3n+1`. -/
private theorem sum_Ico_a (n lo hi : ℕ) (hlo : lo = (n + 1) / 2) (hhi : hi = n + 1) :
    ∑ j ∈ Ico lo hi, a j = 3 * n + 1 := by
  have h := a_rec n
  have hfilter : (range (n + 1)).filter (fun j => n ≤ 2 * j) = Ico lo hi := by
    ext j; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [← hfilter, Finset.sum_filter, Finset.sum_range_succ, if_pos (by omega)]
  linarith

/-- `a(2m+2) = 3`. -/
private theorem a_even (m : ℕ) : a (2 * m + 2) = 3 := by
  have h1 := sum_Ico_a (2 * m + 1) (m + 1) (2 * m + 2) (by omega) (by omega)
  have h2 := sum_Ico_a (2 * m + 2) (m + 1) (2 * m + 2 + 1) (by omega) (by omega)
  rw [Finset.sum_Ico_succ_top (by omega : m + 1 ≤ 2 * m + 2)] at h2
  push_cast at h1 h2
  linarith

/-- `a(2m+1) = a(m) + 3`. -/
private theorem a_odd (m : ℕ) : a (2 * m + 1) = a m + 3 := by
  have h1 := sum_Ico_a (2 * m) m (2 * m + 1) (by omega) (by omega)
  have h2 := sum_Ico_a (2 * m + 1) (m + 1) (2 * m + 1 + 1) (by omega) (by omega)
  rw [Finset.sum_Ico_succ_top (by omega : m + 1 ≤ 2 * m + 1)] at h2
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : m < 2 * m + 1)] at h1
  push_cast at h1 h2
  linarith

/-- `a(0) = 1`. -/
private theorem a_zero : a 0 = 1 := by
  have h := a_rec 0
  simpa using h

/-- The morphism in a uniform shape: `sigma x = [1, b]` with `b = 1` iff `x = 0`. -/
private theorem sigma_eq (x : ℕ) : sigma x = [1, if x = 0 then 1 else 0] := by
  unfold sigma; split <;> simp_all

/-- Even positions of `l.flatMap sigma` carry the letter `1`. -/
private theorem flatMap_getD_even (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    (l.flatMap sigma).getD (2 * i) 0 = 1 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x t ih =>
    rw [List.flatMap_cons, sigma_eq]
    cases i with
    | zero => rfl
    | succ i =>
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
      simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
      exact ih i (by simp at hi; omega)

/-- Position `2i+1` of `l.flatMap sigma` is `1` if position `i` of `l` is `0`, else `0`. -/
private theorem flatMap_getD_odd (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    (l.flatMap sigma).getD (2 * i + 1) 0 = if l.getD i 0 = 0 then 1 else 0 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x t ih =>
    rw [List.flatMap_cons, sigma_eq]
    cases i with
    | zero => rfl
    | succ i =>
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring]
      simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
      exact ih i (by simp at hi; omega)

/-- `m + 1 ≤ 2^m`. -/
private theorem succ_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self

/-- `A035263(2m+1) = 1`. -/
private theorem A035263_odd_index (m : ℕ) : A035263 (2 * m + 1) = 1 := by
  have hk : 2 * m + 1 ≤ 2 ^ (m + 1) := by
    have := succ_le_two_pow m; rw [pow_succ]; omega
  rw [A035263_eq (n := 2 * m + 1) (k := m + 1) (by omega) hk, word,
    show 2 * m + 1 - 1 = 2 * m by omega]
  exact flatMap_getD_even _ _ (by rw [word_length]; exact Nat.lt_two_pow_self)

/-- `A035263(2m+2) = 1` if `A035263(m+1) = 0`, and `0` otherwise. -/
private theorem A035263_even_index (m : ℕ) :
    A035263 (2 * m + 2) = if A035263 (m + 1) = 0 then 1 else 0 := by
  have hk : 2 * m + 2 ≤ 2 ^ (m + 1) := by
    have := succ_le_two_pow m; rw [pow_succ]; omega
  rw [A035263_eq (n := 2 * m + 2) (k := m + 1) (by omega) hk, word,
    show 2 * m + 2 - 1 = 2 * m + 1 by omega,
    flatMap_getD_odd _ _ (by rw [word_length]; exact Nat.lt_two_pow_self),
    A035263_eq (n := m + 1) (k := m) (by omega) (succ_le_two_pow m),
    show m + 1 - 1 = m by omega]

/-- Barry's conjecture: `a(n) mod 2 = A035263(n+1)` for every `n ≥ 0`. -/
theorem result : statement := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [A035263_odd_index m]
      cases m with
      | zero => rw [Nat.mul_zero, a_zero]; rfl
      | succ m => rw [show 2 * (m + 1) = 2 * m + 2 by ring, a_even]; rfl
    · have ihm := ih m (by omega)
      rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, A035263_even_index, a_odd]
      split_ifs with h
      · rw [h] at ihm
        push_cast at ihm ⊢
        omega
      · have h' : (A035263 (m + 1) : ℤ) ≠ 0 := by exact_mod_cast h
        push_cast
        omega

end Math0.Frontier.A127752

#math0_settles Math0.Frontier.A127752.result Math0.Statements.A127752.statement
