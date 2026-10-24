/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A334595: right diagonal of the XOR-triangle of the binary expansion of `n`

Source: https://oeis.org/A334595, Peter Kagey, May 07 2020 (COMMENTS section). Verbatim:
> Conjecture: Records occur at 1 and at 2^n + 1.
>
> Conjecture: a(n) = 1 if and only if n is a power of two.

The sequence (offset `1`) is "Binary interpretation of the right diagonal of the XOR-triangle
with first row generated from the binary expansion of n", where "An XOR-triangle is an inverted
0-1 triangle formed by choosing a top row and having each entry in the subsequent rows be the
XOR of the two values above it." Example from the entry: for `n = 19 = 10011₂` the triangle is
`10011 / 1010 / 111 / 00 / 0`, and "Reading the right side of the triangle starting from the
upper-right corner gives 10100 which is the binary representation of 20 = a(19)."

## Encoding

* `binExp n` is the binary expansion of `n`, most significant bit first, i.e. the reverse of
  `Nat.digits 2 n` (so `binExp 19 = [1, 0, 0, 1, 1]`; `binExp 0 = []`). Its entries are `0` or
  `1`, and on `{0, 1}` the bitwise `x ^^^ y` is exactly XOR.
* `xorRow row` is the next row of the XOR-triangle: entry `i` is `row[i] ^^^ row[i+1]`, so it is
  one shorter than `row`. `triangle row` lists the `row.length` rows
  `row, xorRow row, xorRow (xorRow row), …` (the last one has length `1`), and `rightDiag row`
  is the list of last entries of these rows, i.e. the right side of the triangle read from the
  upper-right corner downwards.
* `a n` reads `rightDiag (binExp n)` as a binary numeral whose first entry is the most
  significant bit (`Nat.ofDigits 2` takes the least significant digit first, hence the
  `reverse`). This is exactly the PARI program in the entry. `triangle_19` and `a_19` check the
  worked example, and `a_data` checks all 70 listed terms `a 1, …, a 70`.
* The sequence has offset `1`, so both conjectures are about indices `n ≥ 1` (the value `a 0 = 0`
  of the encoding plays no role).
* "Records": following the usual OEIS convention, `n ≥ 1` is a record position (`IsRecord n`)
  when `a n` is strictly larger than every earlier term `a m`, `1 ≤ m < n`. "Records occur at 1
  and at 2^n + 1" is read as: the set of record positions is exactly
  `{1} ∪ {2^k + 1 : k ≥ 1}`. The exponent ranges over `k ≥ 1`, like the index `n` of the sequence
  that the conjecture reuses as the exponent's name (offset `1`); `2^0 + 1 = 2` is not a record
  since `a 2 = a 1 = 1`, and `1` is listed separately in the conjecture.
* "a(n) = 1 if and only if n is a power of two" is stated for every `n ≥ 1`, with "power of two"
  meaning `n = 2^k` for some `k ≥ 0` (so `n = 1 = 2^0` is included; `a 1 = 1`).
* `statement` is the conjunction of the two conjectures (`statement_records` and
  `statement_powTwo`).
-/

namespace Math0.Statements.A334595

/-- The binary expansion of `n`, most significant bit first (`binExp 19 = [1, 0, 0, 1, 1]`). -/
def binExp (n : ℕ) : List ℕ := (Nat.digits 2 n).reverse

/-- The next row of an XOR-triangle: each entry is the XOR of the two entries above it (the
entries are `0`/`1`, for which `^^^` is XOR). -/
def xorRow (row : List ℕ) : List ℕ := List.zipWith (fun x y => x ^^^ y) row row.tail

/-- The XOR-triangle with first row `row`: the rows `xorRow^[r] row` for `r < row.length`. -/
def triangle (row : List ℕ) : List (List ℕ) :=
  (List.range row.length).map (fun r => xorRow^[r] row)

/-- The right side of the XOR-triangle with first row `row`, read from the upper-right corner:
the last entry of each row, top to bottom. -/
def rightDiag (row : List ℕ) : List ℕ := (triangle row).map (fun r => r.getLastD 0)

/-- A334595: the binary interpretation (first entry = most significant bit) of the right
diagonal of the XOR-triangle whose first row is the binary expansion of `n`. -/
def a (n : ℕ) : ℕ := Nat.ofDigits 2 (rightDiag (binExp n)).reverse

/-- The worked example of the entry: the XOR-triangle of `19 = 10011₂` (kernel-checked). -/
theorem triangle_19 :
    triangle (binExp 19) = [[1, 0, 0, 1, 1], [1, 0, 1, 0], [1, 1, 1], [0, 0], [0]] := by
  decide +kernel

/-- The worked example of the entry: `a(19) = 20 = 10100₂` (kernel-checked). -/
theorem a_19 : rightDiag (binExp 19) = [1, 0, 1, 0, 0] ∧ a 19 = 20 := by
  decide +kernel

/-- The definition reproduces all 70 terms listed in OEIS, `a 1, …, a 70` (kernel-checked). -/
theorem a_data : (List.range 70).map (fun i => a (i + 1)) =
    [1, 1, 2, 1, 6, 3, 4, 1, 14, 4, 11, 2, 13, 7, 8, 1, 30, 11, 20, 7, 24, 13, 18, 3, 28, 9, 22,
      5, 26, 15, 16, 1, 62, 20, 43, 13, 50, 24, 39, 5, 58, 16, 47, 9, 54, 28, 35, 2, 61, 23, 40,
      14, 49, 27, 36, 6, 57, 19, 44, 10, 53, 31, 32, 1, 126, 43, 84, 24, 103, 50] := by
  decide +kernel

/-- `n` is a record position of the sequence (offset `1`): `n ≥ 1` and `a n` is strictly larger
than every earlier term `a m`, `1 ≤ m < n`. -/
def IsRecord (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → m < n → a m < a n

/-- First conjecture (Peter Kagey, 2020): the records occur exactly at `1` and at `2^k + 1` for
`k ≥ 1`, i.e. at `1, 3, 5, 9, 17, 33, …`. -/
def statement_records : Prop :=
  ∀ n : ℕ, IsRecord n ↔ (n = 1 ∨ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k + 1)

/-- Second conjecture (Peter Kagey, 2020): for `n ≥ 1`, `a(n) = 1` if and only if `n` is a power
of two. -/
def statement_powTwo : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ ∃ k : ℕ, n = 2 ^ k)

/-- Both conjectures of A334595: the record positions are exactly `1` and the numbers `2^k + 1`
(`k ≥ 1`), and for `n ≥ 1`, `a(n) = 1` if and only if `n` is a power of two. -/
def statement : Prop :=
  statement_records ∧ statement_powTwo

end Math0.Statements.A334595
