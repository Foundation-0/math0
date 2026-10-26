/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A334592: zeros in the XOR-triangle of the binary expansion of `n`; records at powers of 2

Source: https://oeis.org/A334592, Peter Kagey, May 07 2020 (COMMENTS section). Verbatim:
> Conjecture: Records occur at powers of two.

The sequence (offset `1`) is "Number of zeros in XOR-triangle with first row generated from the
binary expansion of n", where "An XOR-triangle is an inverted 0-1 triangle formed by choosing a
top row and having each entry in the subsequent rows be the XOR of the two values above it."
(Example from the entry: `53 = 110101₂` gives the rows `110101, 01111, 1000, 100, 10, 1`, which
contain `9` zeros, so `a(53) = 9`.)

## Encoding

* `binary n` is the binary expansion of `n`, most significant bit first, as a `List Bool`
  (`true` = digit `1`). It is computed with a fuel argument so that the kernel can evaluate it;
  `binary_eq_digits` proves that it is exactly the reversed `Nat.digits 2 n` with digits `1`
  read as `true` and `0` as `false`.
* `xorRow r` is the row below `r`: the XOR of each pair of adjacent entries of `r` (length one
  less). `xorTriangle r` is the list of rows `r, xorRow r, xorRow (xorRow r), …` down to the row
  of length `1` (the triangle has `r.length` rows, as in the Mathematica program of the entry,
  which iterates while the row has length `> 1`). `a n` is the total number of `false` entries
  (zeros) over all rows of `xorTriangle (binary n)`. The value `a 0 = 0` is outside the OEIS
  range and is never used by `statement`.
* `a_data` checks all 77 listed terms `a 1, …, a 77`; `triangle_53` checks the triangle of the
  example `n = 53`.
* "Records": following the OEIS convention, `n` (in the range `n ≥ 1` of the sequence) is a
  record position when `a n` is strictly larger than every earlier term, i.e. `a m < a n` for all
  `1 ≤ m < n` (so `n = 1` is a record). Strictness matters: with non-strict records `n = 3`
  (`a 3 = a 2 = 1`) would be a record.
* Reading of "Records occur at powers of two": the record positions are exactly the powers of
  two, i.e. for every `n`, `n` is a record position iff `n = 2^k` for some `k ≥ 0`. The weaker
  one-directional reading (every record position is a power of two) is `statement_weak`, implied
  by `statement` (`statement_imp_weak`); it is not the primary formalization.
-/

namespace Math0.Statements.A334592

/-- Binary digits of `n`, least significant first, computed with `fuel` steps (the fuel is
never exhausted when `n ≤ fuel`, see `bitsLE_eq_digits`). -/
def bitsLE : ℕ → ℕ → List Bool
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else (n % 2 == 1) :: bitsLE fuel (n / 2)

/-- The binary expansion of `n`, most significant bit first (`true` = `1`, `false` = `0`);
empty for `n = 0`. -/
def binary (n : ℕ) : List Bool := (bitsLE n n).reverse

theorem bitsLE_eq_digits : ∀ (fuel n : ℕ), n ≤ fuel →
    bitsLE fuel n = (Nat.digits 2 n).map (fun d => d == 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this
    simp [bitsLE]
  | succ f ih =>
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [bitsLE]
    · rw [bitsLE, if_neg (by omega), Nat.digits_def' (by norm_num) hpos, List.map_cons,
        ih (n / 2) (by omega)]

/-- `binary n` is the reversed list of base-2 digits of `n` (Mathlib's `Nat.digits 2 n`, which
lists digits least significant first), with `1 ↦ true` and `0 ↦ false`. -/
theorem binary_eq_digits (n : ℕ) :
    binary n = ((Nat.digits 2 n).map (fun d => d == 1)).reverse := by
  rw [binary, bitsLE_eq_digits n n le_rfl]

/-- The next row of an XOR-triangle: each entry is the XOR of the two adjacent entries above
it. -/
def xorRow (r : List Bool) : List Bool := List.zipWith xor r r.tail

/-- The first `k` rows `r, xorRow r, xorRow (xorRow r), …` of the XOR-triangle with top row
`r`. -/
def rows : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | k + 1, r => r :: rows k (xorRow r)

/-- The XOR-triangle with top row `r`: all its rows, of lengths `r.length, r.length - 1, …, 1`. -/
def xorTriangle (r : List Bool) : List (List Bool) := rows r.length r

/-- A334592: the number of zeros in the XOR-triangle whose first row is the binary expansion of
`n` (offset `1`). -/
def a (n : ℕ) : ℕ := ((xorTriangle (binary n)).map (List.count false)).sum

/-- The example of the entry: `53 = 110101₂` and its XOR-triangle (kernel-checked). -/
theorem triangle_53 : xorTriangle (binary 53) =
    [[true, true, false, true, false, true],
     [false, true, true, true, true],
     [true, false, false, false],
     [true, false, false],
     [true, false],
     [true]] := by
  decide +kernel

theorem a_53 : a 53 = 9 := by decide +kernel

/-- The definition reproduces all 77 terms listed in OEIS, `a 1, …, a 77` (kernel-checked). -/
theorem a_data : (List.range 77).map (fun i => a (i + 1)) =
    [0, 1, 1, 3, 2, 2, 3, 6, 4, 5, 3, 5, 3, 4, 6, 10, 7, 6, 7, 7, 8, 5, 6, 8, 7, 6, 5, 7, 6, 7,
      10, 15, 11, 11, 9, 9, 9, 11, 9, 11, 9, 13, 9, 9, 7, 9, 9, 13, 9, 9, 11, 9, 9, 7, 9, 11, 9,
      9, 9, 11, 9, 11, 15, 21, 16, 14, 15, 16, 13, 13, 12, 14, 11, 13, 12, 17, 12] := by
  decide +kernel

/-- `n` is a record position of A334592 (offset `1`): `n ≥ 1` and `a n` is strictly larger than
every earlier term `a m`, `1 ≤ m < n`. -/
def IsRecord (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → m < n → a m < a n

/-- Kagey's conjecture: the records of A334592 occur at the powers of two, i.e. `n` is a record
position if and only if `n = 2^k` for some `k ≥ 0`. -/
def statement : Prop :=
  ∀ n : ℕ, IsRecord n ↔ ∃ k : ℕ, n = 2 ^ k

/-- The weaker one-directional reading (every record position is a power of two). Not the
primary formalization. -/
def statement_weak : Prop :=
  ∀ n : ℕ, IsRecord n → ∃ k : ℕ, n = 2 ^ k

theorem statement_imp_weak : statement → statement_weak :=
  fun h n hn => (h n).1 hn

end Math0.Statements.A334592
