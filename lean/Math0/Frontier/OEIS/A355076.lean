/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A355076
import Math0.Audit

/-!
# Integer partial sums of the Calkin-Wilf ratios `fusc(k)/fusc(k+1)` (A355076)

We prove Rémy Sigrist's conjecture: `∑_{k=0}^{n} fusc(k)/fusc(k+1)` is an integer whenever
`n = 2*4^k - 1` or `n = 2*4^k - 2`.

Write `x_j = fusc(j)/fusc(j+1)` (the Calkin-Wilf sequence). The children of `x_j` are
`x_{2j} = x_j/(1+x_j)` and `x_{2j+1} = 1 + x_j`. By the symmetry
`fusc(2^m + i) = fusc(2^m + j)` for `i + j = 2^m`, the row `{x_j : 2^m ≤ j < 2^(m+1)}` is closed
under `x ↦ 1/x` (reflected order), so `∑_row x/(1+x) = ∑_row 1/(1+x)`, and both equal `2^m/2`.
Hence the row sums satisfy `T(m+1) = T(m) + 2^m + 2^m/2`, `T(0) = 1`, so
`T(m) = (3*2^m - 1)/2`, and `∑_{k < 2^M} x_k = (3*2^M - 3 - M)/2`. For `M = 2k+1` this is the
integer `3*4^k - k - 2`; removing the last term `x_{2^M-1} = M/1` gives the other integer.
-/

namespace Math0.Frontier.A355076
open Math0.Statements.A355076

/-- `fusc n > 0` for `n ≥ 1`. -/
private lemma fusc_pos : ∀ n, 1 ≤ n → 0 < fusc n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [fusc_even]; exact ih k (by omega) (by omega)
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [fusc_one]
      · rw [fusc_odd]; have := ih k (by omega) hk; omega

/-- Symmetry of each row of Stern's diatomic sequence: `fusc(2^m + i) = fusc(2^m + j)` when
`i + j = 2^m`. -/
private lemma fusc_symm : ∀ m i j, i + j = 2 ^ m → fusc (2 ^ m + i) = fusc (2 ^ m + j) := by
  intro m
  induction m with
  | zero =>
    intro i j h
    have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by simp at h; omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide +kernel
  | succ m ih =>
    intro i j h
    have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [hp] at h ⊢
    rcases Nat.even_or_odd' i with ⟨i', rfl | rfl⟩ <;>
      rcases Nat.even_or_odd' j with ⟨j', rfl | rfl⟩
    · rw [show 2 * 2 ^ m + 2 * i' = 2 * (2 ^ m + i') by ring,
        show 2 * 2 ^ m + 2 * j' = 2 * (2 ^ m + j') by ring, fusc_even, fusc_even]
      exact ih i' j' (by omega)
    · omega
    · omega
    · rw [show 2 * 2 ^ m + (2 * i' + 1) = 2 * (2 ^ m + i') + 1 by ring,
        show 2 * 2 ^ m + (2 * j' + 1) = 2 * (2 ^ m + j') + 1 by ring, fusc_odd, fusc_odd]
      have e1 := ih i' (j' + 1) (by omega)
      have e2 := ih (i' + 1) j' (by omega)
      rw [← add_assoc] at e1 e2
      rw [e1, e2, Nat.add_comm]

/-- `fusc (2^M) = 1`. -/
private lemma fusc_two_pow (M : ℕ) : fusc (2 ^ M) = 1 := by
  induction M with
  | zero => decide +kernel
  | succ M ih => rw [pow_succ, mul_comm, fusc_even, ih]

/-- `fusc (2^M - 1) = M`. -/
private lemma fusc_two_pow_sub_one (M : ℕ) : fusc (2 ^ M - 1) = M := by
  induction M with
  | zero => decide +kernel
  | succ M ih =>
    have h1 := Nat.one_le_two_pow (n := M)
    rw [show 2 ^ (M + 1) - 1 = 2 * (2 ^ M - 1) + 1 by rw [pow_succ]; omega, fusc_odd, ih,
      Nat.sub_add_cancel h1, fusc_two_pow]

/-- Splitting a sum over `range (2n)` into even and odd indices. -/
private lemma sum_range_double (h : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), h i = ∑ i ∈ Finset.range n, (h (2 * i) + h (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- The left child: `x_{2j} = fusc j / (fusc j + fusc (j+1))`. -/
private lemma ratio_even (j : ℕ) :
    (fusc (2 * j) : ℚ) / fusc (2 * j + 1) = fusc j / (fusc j + fusc (j + 1)) := by
  rw [fusc_even, fusc_odd]; push_cast; ring

/-- The right child: `x_{2j+1} = x_j + 1`. -/
private lemma ratio_odd (j : ℕ) :
    (fusc (2 * j + 1) : ℚ) / fusc (2 * j + 1 + 1) = fusc j / fusc (j + 1) + 1 := by
  have hpos : (0 : ℚ) < fusc (j + 1) := by exact_mod_cast fusc_pos (j + 1) (by omega)
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, fusc_even, fusc_odd]
  push_cast
  field_simp

/-- Over a row, `∑ x/(1+x) = 2^m/2`, proved by pairing `x` with `1/x` via the row symmetry. -/
private lemma row_left_sum (m : ℕ) :
    ∑ i ∈ Finset.range (2 ^ m),
      (fusc (2 ^ m + i) : ℚ) / (fusc (2 ^ m + i) + fusc (2 ^ m + i + 1)) = 2 ^ m / 2 := by
  set N := 2 ^ m with hN
  have hpos : ∀ i, (0 : ℚ) < fusc (N + i) + fusc (N + i + 1) := by
    intro i
    have : 0 < fusc (N + i + 1) := fusc_pos _ (Nat.le_add_left _ _)
    have : (0 : ℚ) < fusc (N + i + 1) := by exact_mod_cast this
    positivity
  have hsum : ∑ i ∈ Finset.range N,
      ((fusc (N + i) : ℚ) / (fusc (N + i) + fusc (N + i + 1)) +
        (fusc (N + i + 1) : ℚ) / (fusc (N + i) + fusc (N + i + 1))) = N := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ))]
    · simp
    · intro i _
      rw [← add_div, div_self (hpos i).ne']
  have hrefl : ∑ i ∈ Finset.range N,
      (fusc (N + i) : ℚ) / (fusc (N + i) + fusc (N + i + 1)) =
      ∑ i ∈ Finset.range N, (fusc (N + i + 1) : ℚ) / (fusc (N + i) + fusc (N + i + 1)) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have e1 : fusc (N + (N - 1 - i)) = fusc (N + i + 1) := by
      rw [fusc_symm m (N - 1 - i) (i + 1) (by omega), add_assoc]
    have e2 : fusc (N + (N - 1 - i) + 1) = fusc (N + i) := by
      rw [show N + (N - 1 - i) + 1 = N + (N - i) by omega, fusc_symm m (N - i) i (by omega)]
    rw [e1, e2, add_comm ((fusc (N + i + 1) : ℚ))]
  rw [Finset.sum_add_distrib, ← hrefl] at hsum
  have hNq : (N : ℚ) = 2 ^ m := by rw [hN]; push_cast; ring
  rw [hNq] at hsum
  linarith

/-- The row sum `T(m) = ∑_{2^m ≤ j < 2^(m+1)} x_j = (3*2^m - 1)/2`. -/
private lemma row_sum (m : ℕ) :
    ∑ i ∈ Finset.range (2 ^ m), (fusc (2 ^ m + i) : ℚ) / fusc (2 ^ m + i + 1) =
      (3 * 2 ^ m - 1) / 2 := by
  induction m with
  | zero => norm_num [fusc_one, show fusc 2 = 1 from by decide +kernel]
  | succ m ih =>
    rw [show 2 ^ (m + 1) = 2 * 2 ^ m by ring, sum_range_double]
    rw [Finset.sum_congr rfl (g := fun i =>
      ((fusc (2 ^ m + i) : ℚ) / (fusc (2 ^ m + i) + fusc (2 ^ m + i + 1)) +
        ((fusc (2 ^ m + i) : ℚ) / fusc (2 ^ m + i + 1) + 1)))]
    · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, row_left_sum, ih]
      simp
      ring
    · intro i _
      rw [show 2 * 2 ^ m + 2 * i = 2 * (2 ^ m + i) by ring,
        show 2 * 2 ^ m + (2 * i + 1) = 2 * (2 ^ m + i) + 1 by ring, ratio_even, ratio_odd]

/-- `∑_{k < 2^M} x_k = (3*2^M - 3 - M)/2`. -/
private lemma prefix_sum (M : ℕ) :
    ∑ k ∈ Finset.range (2 ^ M), (fusc k : ℚ) / fusc (k + 1) = (3 * 2 ^ M - 3 - M) / 2 := by
  induction M with
  | zero => simp [fusc_zero]
  | succ M ih =>
    rw [show 2 ^ (M + 1) = 2 ^ M + 2 ^ M by ring, Finset.sum_range_add, ih, row_sum]
    push_cast
    ring

/-- Sigrist's conjecture for A355076 holds. -/
theorem result : statement := by
  intro n ⟨k, hk⟩
  have hpow : 2 * 4 ^ k = 2 ^ (2 * k + 1) := by
    rw [pow_succ, pow_mul]; norm_num; ring
  have h1 := Nat.one_le_two_pow (n := 2 * k + 1)
  have hS : ∑ j ∈ Finset.range (2 ^ (2 * k + 1)), (fusc j : ℚ) / fusc (j + 1) =
      ((3 * 4 ^ k - k - 2 : ℤ) : ℚ) := by
    rw [prefix_sum]
    push_cast
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rcases hk with rfl | rfl
  · unfold a
    rw [show 2 * 4 ^ k - 1 + 1 = 2 ^ (2 * k + 1) by omega, hS]
    exact Rat.den_intCast _
  · unfold a
    have hsplit :=
      Finset.sum_range_succ (fun j => (fusc j : ℚ) / fusc (j + 1)) (2 ^ (2 * k + 1) - 1)
    rw [Nat.sub_add_cancel h1, hS, fusc_two_pow_sub_one, fusc_two_pow] at hsplit
    rw [show 2 * 4 ^ k - 2 + 1 = 2 ^ (2 * k + 1) - 1 by omega]
    rw [show ∑ j ∈ Finset.range (2 ^ (2 * k + 1) - 1), (fusc j : ℚ) / fusc (j + 1) =
        ((3 * 4 ^ k - k - 2 - (2 * k + 1) : ℤ) : ℚ) by push_cast at hsplit ⊢; linarith]
    exact Rat.den_intCast _

end Math0.Frontier.A355076

#math0_settles Math0.Frontier.A355076.result Math0.Statements.A355076.statement
