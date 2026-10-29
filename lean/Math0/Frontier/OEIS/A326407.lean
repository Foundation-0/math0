/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A326407
import Math0.Audit

/-!
# Prime-Minesweeper on the A060734 array: `a(n) < 6`, and `a(n) = 5` only at `n = 6`

We prove Tatkiewicz's two conjectures from A326407: for every `n ≥ 1`, `a(n) ≤ 4` unless
`n = 6`, and `a(6) = 5`.

**Checkerboard parity.** `val r c ≡ r + c + 1 (mod 2)`: on and above the diagonal
`(c+1)^2 - r ≡ c + 1 + r`, below it `r^2 + 1 + c ≡ r + 1 + c`. So the cells with `r + c` odd hold
even numbers, and the only even prime `2` sits in the single cell `(1, 0)` (as `pos 2 = (1, 0)`
and `val` is injective). Hence an even-valued cell other than `(1, 0)` is never prime.

**Counting.** For an interior cell `(s+1, t+1)` the 4 diagonal neighbours have one parity of
`i + j` and the 4 orthogonal neighbours the other. If `s + t` is odd the diagonal neighbours are
even-valued, and none of them is `(1, 0)` unless `(s, t) = (1, 0)`, i.e. the cell is `(2, 1)`
holding `6`; if `s + t` is even the orthogonal ones are even-valued and avoid `(1, 0)` unless
the cell is `(1, 1)` (checked directly). Either way at least 4 of the 8 neighbours are not
prime. In row `0` (5 neighbours) and column `0` (5 neighbours) the same parity bookkeeping
excludes at least one neighbour, and the corner `(0, 0)` has only 3 neighbours. So every cell
except `(2, 1)` has at most 4 prime neighbours, while the cell `(2, 1)` of `6` has exactly 5
(namely `2, 3, 5, 7, 11`). Since `6` is not prime, `a(6) = 5`.
-/

namespace Math0.Frontier.A326407
open Math0.Statements.A326407

/-- The numbers in the cells adjacent to the cell `(r, c)` (same shape as `neighbours`). -/
private def nb (r c : ℕ) : List ℕ :=
  (near r).flatMap fun i =>
    (near c).filterMap fun j => if (i, j) = (r, c) then none else some (val i j)

/-- `neighbours n` is `nb` at the cell of `n`. -/
private theorem neighbours_eq (n : ℕ) : neighbours n = nb (pos n).1 (pos n).2 := rfl

/-- `c * c` has the parity of `c`. -/
private theorem mul_self_mod_two (c : ℕ) : c * c % 2 = c % 2 := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [Nat.mul_mod, h]

/-- Checkerboard parity of the array: `val i j ≡ i + j + 1 (mod 2)`. -/
private theorem val_mod_two (i j : ℕ) : val i j % 2 = (i + j + 1) % 2 := by
  unfold val
  split_ifs with h
  · have e : (j + 1) ^ 2 = j * j + 2 * j + 1 := by ring
    rw [e]
    have := mul_self_mod_two j
    omega
  · have e : i ^ 2 = i * i := by ring
    rw [e]
    have := mul_self_mod_two i
    omega

/-- The only cell holding `2` is `(1, 0)`. -/
private theorem val_eq_two {i j : ℕ} (h : val i j = 2) : i = 1 ∧ j = 0 := by
  have := pos_val i j
  rw [h, show pos 2 = (1, 0) by decide +kernel] at this
  simp only [Prod.mk.injEq] at this
  omega

/-- An even-valued cell (`i + j` odd) other than `(1, 0)` does not hold a prime. -/
private theorem not_prime_val {i j : ℕ} (h1 : (i + j) % 2 = 1) (h2 : ¬ (i = 1 ∧ j = 0)) :
    ¬ (val i j).Prime := by
  intro hp
  rcases hp.eq_two_or_odd with h | h
  · exact h2 (val_eq_two h)
  · have := val_mod_two i j
    omega

/-- Counting primes in a list one element at a time. -/
private theorem len_filter_cons (a : ℕ) (l : List ℕ) :
    ((a :: l).filter fun m => m.Prime).length =
      (l.filter fun m => m.Prime).length + (if a.Prime then 1 else 0) := by
  by_cases h : a.Prime <;> simp [h]

/-- Every cell other than `(2, 1)` has at most 4 prime neighbours. -/
private theorem count_le (r c : ℕ) (h : ¬ (r = 2 ∧ c = 1)) :
    ((nb r c).filter fun m => m.Prime).length ≤ 4 := by
  rcases r with _ | s <;> rcases c with _ | t
  · decide +kernel
  · simp [nb, near]
    simp only [len_filter_cons, List.filter_nil, List.length_nil]
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · have h1 : ¬ (val 1 (t + 1 + 1)).Prime := not_prime_val (by omega) (by omega)
      simp only [h1, if_false]
      split_ifs <;> omega
    · have h1 : ¬ (val 0 t).Prime := not_prime_val (by omega) (by omega)
      have h2 : ¬ (val 0 (t + 1 + 1)).Prime := not_prime_val (by omega) (by omega)
      simp only [h1, h2, if_false]
      split_ifs <;> omega
  · simp [nb, near]
    simp only [len_filter_cons, List.filter_nil, List.length_nil]
    rcases Nat.mod_two_eq_zero_or_one s with hs | hs
    · have h1 : ¬ (val s 1).Prime := not_prime_val (by omega) (by omega)
      simp only [h1, if_false]
      split_ifs <;> omega
    · have h1 : ¬ (val (s + 1) 1).Prime := not_prime_val (by omega) (by omega)
      have h2 : ¬ (val (s + 1 + 1) 0).Prime := not_prime_val (by omega) (by omega)
      simp only [h1, h2, if_false]
      split_ifs <;> omega
  · by_cases h0 : s = 0 ∧ t = 0
    · obtain ⟨rfl, rfl⟩ := h0
      decide +kernel
    simp [nb, near]
    simp only [len_filter_cons, List.filter_nil, List.length_nil]
    rcases Nat.mod_two_eq_zero_or_one (s + t) with hst | hst
    · have h1 : ¬ (val s (t + 1)).Prime := not_prime_val (by omega) (by omega)
      have h2 : ¬ (val (s + 1) t).Prime := not_prime_val (by omega) (by omega)
      have h3 : ¬ (val (s + 1) (t + 1 + 1)).Prime := not_prime_val (by omega) (by omega)
      have h4 : ¬ (val (s + 1 + 1) (t + 1)).Prime := not_prime_val (by omega) (by omega)
      simp only [h1, h2, h3, h4, if_false]
      split_ifs <;> omega
    · have h1 : ¬ (val s t).Prime := not_prime_val (by omega) (by omega)
      have h2 : ¬ (val s (t + 1 + 1)).Prime := not_prime_val (by omega) (by omega)
      have h3 : ¬ (val (s + 1 + 1) t).Prime := not_prime_val (by omega) (by omega)
      have h4 : ¬ (val (s + 1 + 1) (t + 1 + 1)).Prime := not_prime_val (by omega) (by omega)
      simp only [h1, h2, h3, h4, if_false]
      split_ifs <;> omega

/-- `a(6) = 5` (kernel-checked). -/
private theorem a_six : a 6 = 5 := by
  decide +kernel

/-- For `n ≥ 1`, `n ≠ 6`, we have `a(n) ≤ 4`. -/
private theorem a_le_four {n : ℕ} (hn : 1 ≤ n) (h6 : n ≠ 6) : a n ≤ 4 := by
  unfold a
  split_ifs with hp
  · norm_num
  · rw [neighbours_eq]
    have hc : ¬ ((pos n).1 = 2 ∧ (pos n).2 = 1) := by
      rintro ⟨h1, h2⟩
      have := val_pos hn
      rw [h1, h2, show val 2 1 = 6 by decide] at this
      exact h6 this.symm
    exact_mod_cast count_le _ _ hc

/-- Both conjectures of A326407: `a(n) < 6` for `n ≥ 1`, and `a(n) = 5 ↔ n = 6`. -/
theorem result : statement := by
  refine ⟨fun n hn => ?_, fun n hn => ⟨fun h5 => ?_, fun h => ?_⟩⟩
  · by_cases h6 : n = 6
    · subst h6; rw [a_six]; norm_num
    · have := a_le_four hn h6; omega
  · by_contra h6
    have := a_le_four hn h6; omega
  · subst h; exact a_six

end Math0.Frontier.A326407

#math0_settles Math0.Frontier.A326407.result Math0.Statements.A326407.statement
