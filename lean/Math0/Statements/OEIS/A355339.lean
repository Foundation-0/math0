/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A355339: central even terms in the knight-move triangle A355320

Source: https://oeis.org/A355339, _Rémy Sigrist_, Jun 29 2022 (FORMULA section). Verbatim:
> Conjecture: a(n) = 1 iff n > 0 and n belongs to A000918.

The entry's definition (offset `0`): "a(n) is the number of central even terms in the n-th row
of triangle A355320; a(0) = 0." A355320 is the "Irregular triangle T(n, k), n >= 0,
-2*n <= k <= 2*n, read by rows; T(0, 0) = 1; for n > 0, T(n, k) is the sum of all terms in
previous rows at one knight's move away." Its FORMULA section makes the knight moves explicit:
"T(n, k) = T'(n-1, k-2) + T'(n-1, k+2) + T'(n-2, k-1) + T'(n-2, k+1) for n > 0 (where T'
extends T with 0's outside its domain of definition)." A000918 is "a(n) = 2^n - 2" (offset `0`,
so its terms are `-1, 0, 2, 6, 14, …`).

## Encoding

* Row `n` of A355320 is stored as the list `row n` of its `4n+1` entries `T(n,-2n), …, T(n,2n)`
  (list index `k + 2n`). Rows are built two at a time (`step`, iterated from the pair
  (row `-1` = `[]`, row `0` = `[1]`)); `step` is the knight-move recurrence written as a sum of
  shifted lists: entry `k` of row `n+1` collects `T(n, k±2)` (list shifts `0` and `4`) and
  `T(n-1, k±1)` (list shifts `3` and `5`). This is also the polynomial recurrence
  `R(n+1) = (1+X^4) R(n) + (X^3+X^5) R(n-1)` of the entry's PARI program.
* `T n k` (`k : ℤ`) reads entry `k` of row `n` and is `0` for `|k| > 2n`, i.e. it is the
  zero extension `T'` of the entry. The theorems `T_zero_zero`, `T_eq_zero`, `T_one`,
  `T_add_two` prove that `T` satisfies exactly the defining equations above (the recurrence even
  holds for every `k ∈ ℤ`), and these equations determine `T` by induction on `n`.
  `T_data` checks the 91 listed terms of A355320 (rows `0..6`).
* "The number of central even terms" is read as the size of the maximal block of consecutive
  even entries of row `n` that contains the central position `k = 0` (it is `0` when `T(n,0)`
  is odd). With `right` the number of `k ≥ 0` such that `T(n,0), …, T(n,k)` are all even, and
  `left` the same for `T(n,0), T(n,-1), …, T(n,-k)`, this size is `left + right - 1` when
  `T(n,0)` is even (`k = 0` is counted on both sides) and `0` otherwise. The entry's
  example and its PARI program (`max(0, 2*valuation(r >> (2*n), 2) - 1)`, i.e. `2*right - 1`
  for symmetric rows) agree with this reading. `a 0 = 0` is imposed literally, as in the
  entry (it also follows from `T(0,0) = 1` being odd). `a_eq` restates `a` in terms of `T`.
  `a_data` checks all 77 listed terms `a 0, …, a 76`.
* The conjecture: for every `n ≥ 0` (offset `0`), `a(n) = 1` iff `n > 0` and `n` is a term
  `2^m - 2` (`m ≥ 0`) of A000918. Membership in A000918 is stated in `ℤ`, literally as
  `(n : ℤ) = 2^m - 2`.
-/

namespace Math0.Statements.A355339

/-- Entrywise sum of two lists of naturals, the shorter one padded with zeros. -/
def addL : List ℕ → List ℕ → List ℕ
  | [], l => l
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addL xs ys

/-- From (row `n-1`, row `n`) to (row `n`, row `n+1`): entry `k` of row `n+1` is
`T(n,k+2) + T(n,k-2) + T(n-1,k+1) + T(n-1,k-1)`, written as shifts of the stored lists. -/
def step (pq : List ℕ × List ℕ) : List ℕ × List ℕ :=
  (pq.2, addL (addL pq.2 (List.replicate 4 0 ++ pq.2))
    (addL (List.replicate 3 0 ++ pq.1) (List.replicate 5 0 ++ pq.1)))

/-- `rowPair n = (row (n-1), row n)`, starting from row `-1` (empty, all zeros) and row `0`. -/
def rowPair (n : ℕ) : List ℕ × List ℕ := step^[n] ([], [1])

/-- Row `n` of A355320: the list `T(n,-2n), …, T(n,2n)`. -/
def row (n : ℕ) : List ℕ := (rowPair n).2

/-- Entry `k` of a stored row `r` with index `m` (list position `k + 2m`), `0` outside. -/
def entry (r : List ℕ) (m : ℕ) (k : ℤ) : ℕ :=
  if 0 ≤ k + 2 * m then r.getD (k + 2 * m).toNat 0 else 0

/-- The triangle A355320, `T(n, k)`, extended by `0` outside `-2n ≤ k ≤ 2n`. -/
def T (n : ℕ) (k : ℤ) : ℕ := entry (row n) n k

/-! ### `T` satisfies the defining equations of A355320 -/

theorem getD_addL : ∀ (l₁ l₂ : List ℕ) (i : ℕ),
    (addL l₁ l₂).getD i 0 = l₁.getD i 0 + l₂.getD i 0
  | [], l, i => by simp [addL]
  | x :: xs, [], i => by simp [addL]
  | x :: xs, y :: ys, 0 => by simp [addL]
  | x :: xs, y :: ys, i + 1 => by
    simp only [addL, List.getD_cons_succ]; exact getD_addL xs ys i

theorem length_addL : ∀ (l₁ l₂ : List ℕ), (addL l₁ l₂).length = max l₁.length l₂.length
  | [], l => by simp [addL]
  | x :: xs, [] => by simp [addL]
  | x :: xs, y :: ys => by simp [addL, length_addL xs ys, Nat.succ_max_succ]

theorem getD_replicate_append (l : List ℕ) :
    ∀ (j i : ℕ), (List.replicate j 0 ++ l).getD i 0 = if i < j then 0 else l.getD (i - j) 0
  | 0, i => by simp
  | j + 1, 0 => by simp
  | j + 1, i + 1 => by
    rw [List.replicate_succ, List.cons_append, List.getD_cons_succ, getD_replicate_append l j i]
    simp only [Nat.add_lt_add_iff_right, Nat.add_sub_add_right]

theorem rowPair_succ (n : ℕ) : rowPair (n + 1) = step (rowPair n) :=
  Function.iterate_succ_apply' step n ([], [1])

theorem rowPair_succ_fst (n : ℕ) : (rowPair (n + 1)).1 = row n := by
  rw [rowPair_succ]; rfl

theorem row_succ (n : ℕ) : row (n + 1) =
    addL (addL (row n) (List.replicate 4 0 ++ row n))
      (addL (List.replicate 3 0 ++ (rowPair n).1) (List.replicate 5 0 ++ (rowPair n).1)) := by
  unfold row; rw [rowPair_succ]; rfl

theorem length_rowPair (n : ℕ) :
    (rowPair n).2.length = 4 * n + 1 ∧ (rowPair n).1.length ≤ 4 * n := by
  induction n with
  | zero => simp [rowPair]
  | succ n ih =>
    have h2 := row_succ n
    unfold row at h2
    rw [h2, rowPair_succ_fst]
    unfold row
    simp only [length_addL, List.length_append, List.length_replicate]
    omega

theorem length_row (n : ℕ) : (row n).length = 4 * n + 1 := (length_rowPair n).1

theorem entry_of_eq (r : List ℕ) (m : ℕ) (k : ℤ) (i c : ℕ) (h : k + 2 * m = (i : ℤ) - c) :
    entry r m k = if i < c then 0 else r.getD (i - c) 0 := by
  unfold entry
  split_ifs with h1 h2 h2
  · omega
  · have h3 : k + 2 * m = ((i - c : ℕ) : ℤ) := by omega
    rw [h3, Int.toNat_natCast]
  · rfl
  · omega

theorem entry_of_neg (r : List ℕ) (m : ℕ) (k : ℤ) (h : k + 2 * m < 0) : entry r m k = 0 := by
  unfold entry; rw [if_neg (by omega)]

/-- `T(0, 0) = 1`. -/
theorem T_zero_zero : T 0 0 = 1 := by decide +kernel

/-- `T(n, k) = 0` outside `-2n ≤ k ≤ 2n` (`T` is the zero extension `T'`). -/
theorem T_eq_zero (n : ℕ) (k : ℤ) (h : 2 * (n : ℤ) < |k|) : T n k = 0 := by
  unfold T entry
  split_ifs with h1
  · apply List.getD_eq_default
    rw [length_row]
    rcases abs_cases k with ⟨hk, -⟩ | ⟨hk, -⟩ <;> omega
  · rfl

/-- The knight-move recurrence for `n = 1` (row `-1` does not exist). -/
theorem T_one (k : ℤ) : T 1 k = T 0 (k - 2) + T 0 (k + 2) := by
  unfold T
  rw [row_succ]
  have hp : (rowPair 0).1 = [] := rfl
  rw [hp]
  rcases lt_or_ge (k + 2 * ((0 + 1 : ℕ) : ℤ)) 0 with hk | hk
  · rw [entry_of_neg _ _ _ hk, entry_of_neg _ _ _ (by omega),
      entry_of_neg _ _ _ (by omega)]
  · obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le hk
    rw [entry_of_eq _ _ _ i 0 (by omega), entry_of_eq _ _ _ i 4 (by omega),
      entry_of_eq _ _ _ i 0 (by omega)]
    simp only [Nat.not_lt_zero, if_false, Nat.sub_zero, getD_addL, getD_replicate_append,
      List.getD_nil]
    split_ifs <;> omega

/-- The knight-move recurrence for `n ≥ 2`:
`T(n+2, k) = T(n+1, k-2) + T(n+1, k+2) + T(n, k-1) + T(n, k+1)`, for every `k ∈ ℤ`. -/
theorem T_add_two (n : ℕ) (k : ℤ) :
    T (n + 2) k = T (n + 1) (k - 2) + T (n + 1) (k + 2) + T n (k - 1) + T n (k + 1) := by
  unfold T
  rw [row_succ (n + 1), rowPair_succ_fst]
  rcases lt_or_ge (k + 2 * ((n + 1 + 1 : ℕ) : ℤ)) 0 with hk | hk
  · rw [entry_of_neg _ _ _ (by omega), entry_of_neg _ _ _ (by omega),
      entry_of_neg _ _ _ (by omega), entry_of_neg _ _ _ (by omega),
      entry_of_neg _ _ _ (by omega)]
  · obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le hk
    rw [entry_of_eq _ _ _ i 0 (by omega), entry_of_eq _ _ _ i 4 (by omega),
      entry_of_eq _ _ _ i 0 (by omega), entry_of_eq _ _ _ i 5 (by omega),
      entry_of_eq _ _ _ i 3 (by omega)]
    simp only [Nat.not_lt_zero, if_false, Nat.sub_zero, getD_addL, getD_replicate_append]
    split_ifs <;> omega

/-- `T` reproduces the 91 terms of A355320 listed in OEIS (rows `0..6`; kernel-checked). -/
theorem T_data :
    (List.range 7).flatMap (fun n => (List.range (4 * n + 1)).map fun i => T n (i - 2 * n)) =
      [1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 2, 1, 0, 0, 1, 1, 0, 0, 2, 3, 2, 0, 2, 3, 2, 0, 0, 1, 1, 0,
        0, 3, 4, 3, 1, 6, 8, 6, 1, 3, 4, 3, 0, 0, 1, 1, 0, 0, 4, 5, 4, 3, 12, 16, 12, 6, 12, 16,
        12, 3, 4, 5, 4, 0, 0, 1, 1, 0, 0, 5, 6, 5, 6, 20, 27, 21, 18, 33, 44, 33, 18, 21, 27, 20,
        6, 5, 6, 5, 0, 0, 1] := by
  decide +kernel

/-! ### The sequence A355339 -/

/-- A355339: `a(n)` is the number of central even terms in row `n` of A355320, i.e. the size of
the maximal block of consecutive even entries `T(n, k)` containing `k = 0` (`0` if `T(n, 0)` is
odd); `a(0) = 0`. Here `right` counts the `k ∈ {0, …, 2n}` with `T(n,0), …, T(n,k)` all even,
`left` counts the `k ∈ {0, …, 2n}` with `T(n,0), T(n,-1), …, T(n,-k)` all even, and the block is
`{-(left-1), …, right-1}`. (The row is bound once as `r`, so that `entry r n k = T n k`; see
`a_eq`.) -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    let r := row n
    let right := (((List.range (2 * n + 1)).map fun k : ℕ => entry r n k).takeWhile
      fun x => x % 2 == 0).length
    let left := (((List.range (2 * n + 1)).map fun k : ℕ => entry r n (-k)).takeWhile
      fun x => x % 2 == 0).length
    if right = 0 then 0 else left + right - 1

/-- `a` written directly in terms of the triangle `T`. -/
theorem a_eq (n : ℕ) : a n =
    if n = 0 then 0 else
      let right := (((List.range (2 * n + 1)).map fun k : ℕ => T n k).takeWhile
        fun x => x % 2 == 0).length
      let left := (((List.range (2 * n + 1)).map fun k : ℕ => T n (-k)).takeWhile
        fun x => x % 2 == 0).length
      if right = 0 then 0 else left + right - 1 := rfl

/-- The definition reproduces the first terms listed in OEIS (kernel-checked): all 77 listed
terms `a 0, …, a 76`. -/
theorem a_data : (List.range 77).map (fun i => a (i + 0)) =
    [0, 3, 1, 3, 3, 7, 1, 3, 5, 3, 5, 11, 3, 11, 1, 3, 5, 7, 7, 3, 5, 7, 9, 19, 7, 3, 5, 19, 3,
      11, 1, 3, 5, 7, 9, 11, 13, 11, 7, 3, 5, 7, 9, 11, 13, 15, 17, 35, 15, 11, 7, 3, 5, 7, 9,
      35, 7, 3, 5, 19, 3, 11, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 23, 19, 15] := by
  decide +kernel

/-- Sigrist's conjecture (A355339, FORMULA section): for every `n ≥ 0`, `a(n) = 1` if and only
if `n > 0` and `n` is a term of A000918, i.e. `n = 2^m - 2` for some `m ≥ 0`. -/
def statement : Prop :=
  ∀ n : ℕ, a n = 1 ↔ (0 < n ∧ ∃ m : ℕ, (n : ℤ) = 2 ^ m - 2)

end Math0.Statements.A355339
