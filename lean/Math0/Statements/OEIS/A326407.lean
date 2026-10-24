/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A326407: prime-Minesweeper on the A060734 square array, `a(n) < 6`, `a(n) = 5` only at `6`

Source: https://oeis.org/A326407, _Witold Tatkiewicz_, Oct 02 2019. Verbatim (COMMENTS):
> a(n) < 6 (conjectured).
>
> a(n) = 5 for n={6} (conjectured).

(The entry also has a third comment, "Set of n such that a(n) = 4 is unbounded (conjectured).",
which is not part of `statement`; it is recorded separately as `statement_four_unbounded`.)

The entry's definition (offset 1): "Minesweeper sequence of positive integers arranged on a 2D
grid along a square array that grows by alternately adding a row at its bottom edge and a column
at its right edge." "Place positive integers on a 2D grid starting with 1 in the top left corner
and continue along an increasing square array as in A060734. Replace each prime with -1 and each
nonprime with the number of primes in adjacent grid cells around them. n is replaced by a(n)."
The example shows the array
```
  1  4  9 16 25 36
  2  3  8 15 24 35
  5  6  7 14 23 34
 10 11 12 13 22 33
 17 18 19 20 21 32
 26 27 28 29 30 31
```

## Encoding

* `val r c` is the entry in row `r`, column `c` (both 0-indexed, row 0 on top, column 0 on the
  left): `(c + 1)^2 - r` if `r ≤ c` and `r^2 + 1 + c` if `r > c`. `val_data` checks it against
  the first 66 terms of A060734 (the array read by antidiagonals downwards) and against the
  array of the example.
* `pos n` is the cell holding `n ≥ 1`, computed with `k = Nat.sqrt (n - 1)` (the cell lies on the
  `k`-th "hook" `max r c = k`). `pos_val` and `val_pos` prove that `val` and `pos` are mutually
  inverse bijections between `ℕ × ℕ` and the positive integers, so every positive integer occurs
  exactly once in the array.
* "Adjacent grid cells" are the Minesweeper neighbours: the cells `(i, j) ≠ (r, c)` with
  `|i - r| ≤ 1` and `|j - c| ≤ 1` that lie in the grid (`i, j ≥ 0`), so there are 8 of them in
  general, 5 on the top row or left column and 3 at the corner `(0, 0)`. `near x` lists the
  admissible coordinates within distance 1 of `x`, and `neighbours n` lists the values in the
  neighbouring cells of `pos n` (without repetitions, since `val` is injective by `pos_val`).
* `a n : ℤ` is `-1` if `n` is prime and otherwise the number of primes among `neighbours n`.
  It is meaningful for `n ≥ 1` (offset 1); `a 0` is a junk value. `a_data` checks all 81 listed
  terms `a 1, …, a 81`.
* The two conjectures are stated over the whole range `n ≥ 1` of the sequence:
  `a n < 6` for every `n ≥ 1`, and, for `n ≥ 1`, `a n = 5` iff `n = 6` (the set of `n` with
  `a(n) = 5` is exactly `{6}`).
-/

namespace Math0.Statements.A326407

/-- The entry in row `r`, column `c` (0-indexed) of the A060734 array:
`(c + 1)^2 - r` on and above the diagonal (`r ≤ c`), `r^2 + 1 + c` below it (`r > c`). -/
def val (r c : ℕ) : ℕ := if r ≤ c then (c + 1) ^ 2 - r else r ^ 2 + 1 + c

/-- The cell `(row, column)` holding `n ≥ 1` in the A060734 array. With `k = ⌊√(n-1)⌋`,
the numbers `k^2 + 1, …, k^2 + k` fill row `k` from the left (columns `0, …, k - 1`) and
`k^2 + k + 1, …, (k+1)^2` fill column `k` from the bottom (rows `k, …, 0`). -/
def pos (n : ℕ) : ℕ × ℕ :=
  if n ≤ Nat.sqrt (n - 1) ^ 2 + Nat.sqrt (n - 1) then
    (Nat.sqrt (n - 1), n - Nat.sqrt (n - 1) ^ 2 - 1)
  else ((Nat.sqrt (n - 1) + 1) ^ 2 - n, Nat.sqrt (n - 1))

/-- `pos` inverts `val`: in particular `val` is injective. -/
theorem pos_val (r c : ℕ) : pos (val r c) = (r, c) := by
  unfold val
  split_ifs with h
  · have e : (c + 1) ^ 2 = c * c + 2 * c + 1 := by ring
    have e2 : c ^ 2 = c * c := by ring
    have hs : Nat.sqrt ((c + 1) ^ 2 - r - 1) = c := by
      rw [e, show c * c + 2 * c + 1 - r - 1 = c * c + (2 * c - r) by omega]
      exact Nat.sqrt_add_eq c (by omega)
    unfold pos
    rw [hs, e, e2, if_neg (by omega)]
    rw [Prod.mk.injEq]; omega
  · have e : (r + 1) ^ 2 = r * r + 2 * r + 1 := by ring
    have e2 : r ^ 2 = r * r := by ring
    have hs : Nat.sqrt (r ^ 2 + 1 + c - 1) = r := by
      rw [e2, show r * r + 1 + c - 1 = r * r + c by omega]
      exact Nat.sqrt_add_eq r (by omega)
    unfold pos
    rw [hs, e2, if_pos (by omega)]
    rw [Prod.mk.injEq]; omega

/-- `val` inverts `pos` on the positive integers: every `n ≥ 1` occurs in the array. -/
theorem val_pos {n : ℕ} (hn : 1 ≤ n) : val (pos n).1 (pos n).2 = n := by
  have h1 := Nat.sqrt_le (n - 1)
  have h2 := Nat.lt_succ_sqrt (n - 1)
  unfold pos
  generalize Nat.sqrt (n - 1) = k at h1 h2 ⊢
  have e : (k + 1) ^ 2 = k * k + 2 * k + 1 := by ring
  have e2 : k ^ 2 = k * k := by ring
  have e3 : Nat.succ k * Nat.succ k = k * k + 2 * k + 1 := by rw [Nat.succ_eq_add_one]; ring
  rw [e3] at h2
  rw [e, e2]
  split_ifs with h
  · unfold val
    rw [e2, if_neg (by omega)]
    omega
  · unfold val
    rw [e, if_pos (by omega)]
    omega

/-- The coordinates at distance at most 1 from `x` that are still in the grid (`≥ 0`). -/
def near (x : ℕ) : List ℕ := if x = 0 then [0, 1] else [x - 1, x, x + 1]

/-- The numbers in the grid cells adjacent to the cell of `n` (horizontally, vertically or
diagonally, as in Minesweeper): up to 8 of them, fewer on the border of the grid. -/
def neighbours (n : ℕ) : List ℕ :=
  (near (pos n).1).flatMap fun i =>
    (near (pos n).2).filterMap fun j =>
      if (i, j) = pos n then none else some (val i j)

/-- A326407 (offset 1): `-1` if `n` is prime, otherwise the number of primes in the grid cells
adjacent to the cell of `n` in the A060734 array. -/
def a (n : ℕ) : ℤ :=
  if n.Prime then -1 else (((neighbours n).filter fun m => m.Prime).length : ℤ)

/-- `val` reproduces the 66 listed terms of A060734 (the array read by antidiagonals downwards,
i.e. `val 0 d, val 1 (d - 1), …, val d 0` for `d = 0, …, 10`), and the 6 × 6 array of the
A326407 example (kernel-checked). -/
theorem val_data :
    ((List.range 11).flatMap fun d => (List.range (d + 1)).map fun i => val i (d - i)) =
      [1, 4, 2, 9, 3, 5, 16, 8, 6, 10, 25, 15, 7, 11, 17, 36, 24, 14, 12, 18, 26, 49, 35, 23, 13,
        19, 27, 37, 64, 48, 34, 22, 20, 28, 38, 50, 81, 63, 47, 33, 21, 29, 39, 51, 65, 100, 80,
        62, 46, 32, 30, 40, 52, 66, 82, 121, 99, 79, 61, 45, 31, 41, 53, 67, 83, 101] ∧
    ((List.range 6).map fun r => (List.range 6).map fun c => val r c) =
      [[1, 4, 9, 16, 25, 36], [2, 3, 8, 15, 24, 35], [5, 6, 7, 14, 23, 34],
        [10, 11, 12, 13, 22, 33], [17, 18, 19, 20, 21, 32], [26, 27, 28, 29, 30, 31]] := by
  decide +kernel

/-- The definition reproduces the first terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 81).map (fun i => a (i + 1)) =
    [2, -1, -1, 2, -1, 5, -1, 2, 1, 3, -1, 4, -1, 3, 2, 0, -1, 3, -1, 3, 3, 2, -1, 1, 0, 2, 3, 2,
      -1, 3, -1, 1, 2, 2, 2, 0, -1, 1, 2, 3, -1, 3, -1, 3, 3, 2, -1, 1, 0, 1, 2, 2, -1, 2, 3, 2, 3,
      2, -1, 2, -1, 3, 2, 0, 1, 2, -1, 2, 1, 1, -1, 3, -1, 1, 1, 1, 3, 3, -1, 1, 0] := by
  decide +kernel

/-- Conjectures (Tatkiewicz, A326407): for every `n ≥ 1`, `a(n) < 6`; and `a(n) = 5` holds for
`n = 6` and for no other `n ≥ 1`. -/
def statement : Prop :=
  (∀ n : ℕ, 1 ≤ n → a n < 6) ∧ (∀ n : ℕ, 1 ≤ n → (a n = 5 ↔ n = 6))

/-- The third conjecture of the entry (not part of `statement`): the set of `n` with
`a(n) = 4` is unbounded. -/
def statement_four_unbounded : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a n = 4

end Math0.Statements.A326407
