/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A332010: denominators of the average first letter of derangements with `k` descents

Source: https://oeis.org/A332010, _Peter Kagey_, Feb 04 2020 (COMMENTS section). Verbatim:
> Conjecture: T(n, 1) = 2^(n-2).

The entry's name is "Irregular triangle of denominators of the average value of the first letter
over all derangements of {1, 2, ..., n} with k descents." (keyword `tabf`, offset `2`, i.e. the
rows are `n = 2, 3, …`). Its comments add "Even-indexed rows have length n - 1; odd-indexed rows
have length n - 2." The example: "T(4,1) = 4 because the derangements of four letters with one
descent are [2,3,4,1], [2,4,1,3], [3,4,1,2], and [4,1,2,3], and the expected value of the first
letter is (2+2+3+4)/4 = 11/4, which has 4 as its denominator."

## Encoding

* *Permutations as words.* As in the entry's example, a permutation of `{1, …, n}` is written in
  one-line notation, as the word (list) `w = [w₁, …, wₙ]` of its values. The permutations of
  `{1, …, n}` are enumerated by Mathlib's `List.permutations (List.range' 1 n)`, which lists every
  rearrangement of `[1, 2, …, n]` (`List.mem_permutations`) exactly once
  (`List.nodup_permutations`); `mem_ders` and `nodup_ders` record this for the words used here.
* *Derangement.* `IsDerangement w`: no letter is in its own position, i.e. `w[i] ≠ i + 1` for
  every `0`-based index `i` (position `i + 1`).
* *Descents.* `des w` is the number of adjacent positions with `wᵢ > wᵢ₊₁`, counted over the
  pairs `(wᵢ, wᵢ₊₁)` of `w.zip w.tail`.
* *First letter.* `w.headD 0`; all words used have length `n ≥ 1`, so this is `w₁`.
* *The triangle.* `ders n k` is the list of derangements of `{1, …, n}` with exactly `k`
  descents, `avgFirst n k ∈ ℚ` is the average of their first letters (sum divided by count), and
  `T n k` is its denominator `Rat.den`; a Mathlib rational is always in lowest terms, so this is
  the denominator of the reduced fraction. (When there is no such derangement the average is
  `0 / 0 = 0` and `T n k = 1`, but such `(n, k)` are not entries of the triangle.)
* *Rows.* Row `n ≥ 2` is `T(n, 1), …, T(n, rowLen n)` with `rowLen n = n - 1` for even `n` and
  `n - 2` for odd `n`, as stated in the entry's comment. (Derangements have at least one descent,
  since the only permutation without descents is the identity, and the only permutation with
  `n - 1` descents is the reversal, a derangement exactly when `n` is even.)
* *Data check.* `List.permutations` is defined by well-founded recursion, which the kernel does
  not evaluate well. The kernel copy `rowC` enumerates the words with Mathlib's structurally
  recursive `List.permutations'`, keeps the derangements once (`DC n`, via the recursive test
  `derB`), and splits them by the recursive descent count `desB`. `derB_one` and `desB_eq`
  identify the tests with `IsDerangement` and `des`, and `ders_perm` shows the resulting word
  lists are permutations of `ders n k`, so they give the same count and the same sum of first
  letters (`row_eq_rowC`). `a_data` checks, in the kernel, the 25 listed terms of rows `2` to `8`
  of the triangle read by rows (row `8` runs through all `8! = 40320` words, about a minute; the
  entry's 50 listed terms reach row `11`, whose `11!` words are out of the kernel's reach). These
  include `T(n, 1) = 2^(n-2)` for `2 ≤ n ≤ 8`; `example_T41` checks the entry's worked example.
* *The conjecture.* "T(n, 1) = 2^(n-2)" carries no explicit range; it is read for every row of
  the triangle, i.e. for all `n ≥ 2` (offset `2`; `T(n, 1)` is the first entry of row `n`, and
  every row `n ≥ 2` is nonempty). For `n ≥ 2` the natural-number subtraction `n - 2` is exact.
-/

namespace Math0.Statements.A332010

/-! ### Definitions -/

/-- A word `w = [w₁, …, wₙ]` (a permutation in one-line notation) is a derangement: no letter
is in its own position, i.e. `w[i] ≠ i + 1` for every `0`-based index `i`. -/
def IsDerangement (w : List ℕ) : Prop := ∀ (i : ℕ) (h : i < w.length), w[i] ≠ i + 1

instance : DecidablePred IsDerangement := fun w => by unfold IsDerangement; infer_instance

/-- The number of descents of a word: the number of adjacent pairs `(wᵢ, wᵢ₊₁)` with
`wᵢ > wᵢ₊₁`. -/
def des (w : List ℕ) : ℕ := (w.zip w.tail).countP fun p => p.2 < p.1

/-- The derangements of `{1, 2, …, n}` with exactly `k` descents, in one-line notation (each
listed once, see `mem_ders` and `nodup_ders`). -/
def ders (n k : ℕ) : List (List ℕ) :=
  (List.range' 1 n).permutations.filter fun w => decide (IsDerangement w) && des w == k

/-- The average value of the first letter over a list `E` of words: the sum of their first
letters divided by their number. -/
def avgFirstLetter (E : List (List ℕ)) : ℚ :=
  (((E.map fun w => w.headD 0).sum : ℕ) : ℚ) / ((E.length : ℕ) : ℚ)

/-- The average value of the first letter over all derangements of `{1, 2, …, n}` with `k`
descents. -/
def avgFirst (n k : ℕ) : ℚ := avgFirstLetter (ders n k)

/-- A332010: `T(n, k)` is the denominator (in lowest terms) of the average value of the first
letter over all derangements of `{1, 2, …, n}` with `k` descents. -/
def T (n k : ℕ) : ℕ := (avgFirst n k).den

/-- The length of row `n` of the triangle (entry's comment): `n - 1` for even `n`, `n - 2` for
odd `n`. -/
def rowLen (n : ℕ) : ℕ := if n % 2 = 0 then n - 1 else n - 2

/-- Row `n` of the triangle: `T(n, 1), …, T(n, rowLen n)`. -/
def row (n : ℕ) : List ℕ := (List.range (rowLen n)).map fun j => T n (j + 1)

/-! ### Faithfulness of the word enumeration -/

/-- The words in `ders n k` are exactly the rearrangements of `[1, …, n]` that are derangements
with `k` descents. -/
theorem mem_ders {n k : ℕ} {w : List ℕ} :
    w ∈ ders n k ↔ w.Perm (List.range' 1 n) ∧ IsDerangement w ∧ des w = k := by
  simp [ders, List.mem_permutations]

/-- Each derangement is listed only once in `ders n k`. -/
theorem nodup_ders (n k : ℕ) : (ders n k).Nodup :=
  (List.nodup_permutations _ List.nodup_range').filter _

/-! ### A kernel-friendly copy of the definition -/

/-- `derB w i` checks that the `j`-th letter of `w` (`0`-based) is never `j + i`. -/
def derB : List ℕ → ℕ → Bool
  | [], _ => true
  | x :: xs, i => x != i && derB xs (i + 1)

/-- Structurally recursive count of descents. -/
def desB : List ℕ → ℕ
  | x :: y :: l => (if y < x then 1 else 0) + desB (y :: l)
  | _ => 0

theorem derB_iff (w : List ℕ) (i : ℕ) :
    derB w i = true ↔ ∀ (j : ℕ) (h : j < w.length), w[j] ≠ j + i := by
  induction w generalizing i with
  | nil => simp [derB]
  | cons x xs ih =>
    simp only [derB, Bool.and_eq_true, bne_iff_ne, ne_eq, ih, List.length_cons]
    constructor
    · rintro ⟨hx, h⟩ j hj
      cases j with
      | zero => simpa using hx
      | succ j =>
        have := h j (by omega)
        simp only [List.getElem_cons_succ]
        omega
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun j hj => ?_⟩
      have := h (j + 1) (by omega)
      simp only [List.getElem_cons_succ] at this
      omega

theorem derB_one (w : List ℕ) : derB w 1 = decide (IsDerangement w) := by
  rw [Bool.eq_iff_iff, derB_iff, decide_eq_true_iff]
  rfl

theorem desB_eq : ∀ w : List ℕ, desB w = des w
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by
    rw [desB, desB_eq (y :: l)]
    simp only [des, List.tail_cons, List.zip_cons_cons, List.countP_cons, decide_eq_true_eq]
    omega

/-- The derangements of `{1, …, n}`, enumerated through the structurally recursive
`List.permutations'`. -/
def DC (n : ℕ) : List (List ℕ) := (List.range' 1 n).permutations'.filter fun w => derB w 1

/-- Row `n` computed from a single enumeration `DC n` of the derangements. -/
def rowC (n : ℕ) : List ℕ :=
  (List.range (rowLen n)).map fun j => (avgFirstLetter ((DC n).filter fun w => desB w == j + 1)).den

theorem avgFirstLetter_perm {E F : List (List ℕ)} (h : E.Perm F) :
    avgFirstLetter E = avgFirstLetter F := by
  simp only [avgFirstLetter, h.length_eq, (h.map fun w => w.headD 0).sum_eq]

theorem ders_perm (n k : ℕ) : (ders n k).Perm ((DC n).filter fun w => desB w == k) := by
  rw [DC, List.filter_filter]
  have : (fun w => (desB w == k) && derB w 1) =
      (fun w => decide (IsDerangement w) && des w == k) := by
    funext w
    rw [desB_eq, derB_one, Bool.and_comm]
  rw [this]
  exact (List.permutations_perm_permutations' _).filter _

theorem row_eq_rowC (n : ℕ) : row n = rowC n := by
  unfold row rowC
  congr 1
  funext j
  rw [T, avgFirst, avgFirstLetter_perm (ders_perm n (j + 1))]

/-! ### Sanity checks -/

/-- The entry's example: the derangements of four letters with one descent are `[2,3,4,1]`,
`[2,4,1,3]`, `[3,4,1,2]`, `[4,1,2,3]`, with average first letter `11/4`, so `T(4, 1) = 4`. -/
theorem example_T41 :
    (ders 4 1).Perm [[2, 3, 4, 1], [2, 4, 1, 3], [3, 4, 1, 2], [4, 1, 2, 3]] ∧
      avgFirst 4 1 = 11 / 4 ∧ T 4 1 = 4 := by
  have h : ((DC 4).filter fun w => desB w == 1).Perm
      [[2, 3, 4, 1], [2, 4, 1, 3], [3, 4, 1, 2], [4, 1, 2, 3]] := by decide +kernel
  have h1 : avgFirst 4 1 = 11 / 4 := by
    rw [avgFirst, avgFirstLetter_perm ((ders_perm 4 1).trans h)]
    decide +kernel
  exact ⟨(ders_perm 4 1).trans h, h1, by rw [T, h1]; decide +kernel⟩

/-- The definition reproduces the first 25 listed terms of OEIS, i.e. rows `2` to `8` of the
triangle read by rows (kernel-checked). -/
theorem a_data : (List.range 7).flatMap (fun i => row (i + 2)) =
    [1, 2, 4, 1, 1, 8, 3, 4, 16, 104, 40, 24, 1, 32, 392, 896, 480, 54, 64, 152, 308, 1496, 63,
      108, 1] := by
  simp only [row_eq_rowC]
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Kagey, A332010): `T(n, 1) = 2^(n-2)` for every row `n ≥ 2`, i.e. the average
first letter of the derangements of `{1, …, n}` with exactly one descent has denominator
`2^(n-2)` in lowest terms. -/
def statement : Prop := ∀ n : ℕ, 2 ≤ n → T n 1 = 2 ^ (n - 2)

end Math0.Statements.A332010
