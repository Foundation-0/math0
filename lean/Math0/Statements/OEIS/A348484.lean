/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A348484: squares of an `n × n` board, no two exactly two steps apart in a row or column

Source: https://oeis.org/A348484, _Yang Hong_, Oct 20 2021. Verbatim (FORMULA section):
> Conjectures:
> a(n) = n^2/2 for n == 0 (mod 4).
> a(n) = (n^2 + 1)/2 for n == 1 or 3 (mod 4).
> a(n) = n^2/2 + 2 for n == 2 (mod 4).

The entry's name: "Maximum number of squares on an n X n chessboard such that no two are two
steps apart horizontally or vertically." Offset `1`, so the sequence (and the conjecture)
concerns every `n ≥ 1`.

## Encoding

* A square of the `n × n` board is a pair `(i, j) : Fin n × Fin n` (row, column).
* Two squares are "two steps apart horizontally or vertically" (`TwoApart`) iff they lie in the
  same row and their columns differ by exactly `2`, or they lie in the same column and their rows
  differ by exactly `2`. The entry's examples confirm this reading: for `n = 2` all four squares
  are taken (so diagonal neighbours, at taxicab distance `2`, are allowed), its `n = 4`
  example `1100/1100/0011/0011` takes squares that are two steps apart diagonally, and its
  `n = 5` example row `11001` takes squares three and four steps apart in a row.
* `Admissible S`: no two squares of `S` are two steps apart.
* `a n` is the largest `S.card` over admissible `S ⊆ Fin n × Fin n`, written as a `Finset.sup`
  over all subsets of the board (`∅` is admissible, so this is a genuine maximum).
* In the statement, `/` is natural-number division. Each of the three formulas is exact in its
  case (`n²` is even for even `n`, `n² + 1` is even for odd `n`), so they mean the same as the
  entry's rational expressions. "n == 1 or 3 (mod 4)" is `n % 4 = 1 ∨ n % 4 = 3`.

## Data check

`a` is computable but enumerates all `2^(n²)` subsets of the board, which the kernel cannot do
beyond very small `n`. Each listed value `a n = v` (`n = 1, …, 10`, all 10 listed terms) is
therefore proved from a finite certificate by `a_eq_of_cert`, with every side condition checked
by `decide +kernel`:

* a lower-bound witness: an admissible set of `v` squares (`ofRows n rowsN`, given by row
  bitmasks: square `(i, j)` is taken iff bit `j` of the `i`-th mask is set, so column `0` is
  the rightmost digit of each `0b` literal);
* an upper-bound certificate: a labelling of the `n²` squares by labels `< v` (`labOf n labelsN`,
  a table indexed by row and column) in which any two distinct squares with the same label are
  two steps apart. An admissible set takes at most one square per label, so it has at most `v`
  squares.

Both certificates were found by computer (a maximum matching of the "two steps apart" graph).
They only certify the ten listed terms. As an independent check of the certificate method,
`a_small` evaluates `a 1, a 2, a 3` by brute force straight from the definition.
-/

namespace Math0.Statements.A348484

/-- Two squares of the `n × n` board are two steps apart horizontally or vertically: they are in
the same row with columns differing by exactly `2`, or in the same column with rows differing by
exactly `2`. -/
def TwoApart {n : ℕ} (c d : Fin n × Fin n) : Prop :=
  (c.1 = d.1 ∧ (c.2.val + 2 = d.2.val ∨ d.2.val + 2 = c.2.val)) ∨
    (c.2 = d.2 ∧ (c.1.val + 2 = d.1.val ∨ d.1.val + 2 = c.1.val))

instance {n : ℕ} (c d : Fin n × Fin n) : Decidable (TwoApart c d) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A set of squares of the `n × n` board no two of which are two steps apart horizontally or
vertically. -/
def Admissible {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  ∀ c ∈ S, ∀ d ∈ S, ¬ TwoApart c d

instance {n : ℕ} (S : Finset (Fin n × Fin n)) : Decidable (Admissible S) :=
  inferInstanceAs (Decidable (∀ c ∈ S, ∀ d ∈ S, ¬ TwoApart c d))

/-- A348484: the maximum number of squares on an `n × n` chessboard such that no two are two
steps apart horizontally or vertically (OEIS offset `1`; `a 0 = 0`). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n × Fin n))).filter Admissible).sup Finset.card

/-- Certificate for a value of `a`: an admissible set of `v` squares, and a labelling of the
squares by labels `< v` in which squares with equal labels are equal or two steps apart. -/
theorem a_eq_of_cert {n v : ℕ} (S : Finset (Fin n × Fin n)) (hS : Admissible S)
    (hcard : S.card = v) (lab : Fin n × Fin n → ℕ) (hlt : ∀ c, lab c < v)
    (hfib : ∀ c d, lab c = lab d → c = d ∨ TwoApart c d) : a n = v := by
  apply le_antisymm
  · apply Finset.sup_le
    intro T hT
    have hT' : Admissible T := (Finset.mem_filter.1 hT).2
    have hinj : Set.InjOn lab T := by
      intro c hc d hd h
      rcases hfib c d h with h | h
      · exact h
      · exact absurd h (hT' c hc d hd)
    calc T.card = (T.image lab).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range v).card := Finset.card_le_card fun x hx => by
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
          exact Finset.mem_range.2 (hlt c)
      _ = v := Finset.card_range v
  · rw [← hcard]
    exact Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩)

/-- The squares selected by row bitmasks: `(i, j)` is selected iff bit `j` of `rows[i]` is set. -/
def ofRows (n : ℕ) (rows : List ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun c => (rows.getD c.1 0).testBit c.2

/-- The labelling given by a table: square `(i, j)` gets the label `tab[i][j]`. -/
def labOf (n : ℕ) (tab : List (List ℕ)) (c : Fin n × Fin n) : ℕ :=
  (tab.getD c.1 []).getD c.2 0

/-! ### Certificates for the ten listed terms -/

/-- `a 1 = 1`: the witness `rows1` and the labelling `labels1`. -/
def rows1 : List ℕ := [0b1]

def labels1 : List (List ℕ) :=
  [[0]]

theorem a_1 : a 1 = 1 :=
  a_eq_of_cert (ofRows 1 rows1) (by decide +kernel) (by decide +kernel)
    (labOf 1 labels1) (by decide +kernel) (by decide +kernel)

/-- `a 2 = 4`: the witness `rows2` and the labelling `labels2`. -/
def rows2 : List ℕ :=
  [0b11,
    0b11]

def labels2 : List (List ℕ) :=
  [[0, 1],
    [2, 3]]

theorem a_2 : a 2 = 4 :=
  a_eq_of_cert (ofRows 2 rows2) (by decide +kernel) (by decide +kernel)
    (labOf 2 labels2) (by decide +kernel) (by decide +kernel)

/-- `a 3 = 5`: the witness `rows3` and the labelling `labels3`. -/
def rows3 : List ℕ :=
  [0b100,
    0b110,
    0b011]

def labels3 : List (List ℕ) :=
  [[0, 1, 3],
    [2, 4, 2],
    [0, 1, 3]]

theorem a_3 : a 3 = 5 :=
  a_eq_of_cert (ofRows 3 rows3) (by decide +kernel) (by decide +kernel)
    (labOf 3 labels3) (by decide +kernel) (by decide +kernel)

/-- `a 4 = 8`: the witness `rows4` and the labelling `labels4`. -/
def rows4 : List ℕ :=
  [0b1100,
    0b1100,
    0b0011,
    0b0011]

def labels4 : List (List ℕ) :=
  [[0, 1, 0, 1],
    [2, 3, 2, 3],
    [4, 5, 4, 5],
    [6, 7, 6, 7]]

theorem a_4 : a 4 = 8 :=
  a_eq_of_cert (ofRows 4 rows4) (by decide +kernel) (by decide +kernel)
    (labOf 4 labels4) (by decide +kernel) (by decide +kernel)

/-- `a 5 = 13`: the witness `rows5` and the labelling `labels5`. -/
def rows5 : List ℕ :=
  [0b11001,
    0b01100,
    0b00110,
    0b10011,
    0b11001]

def labels5 : List (List ℕ) :=
  [[12, 0, 1, 0, 1],
    [2, 3, 4, 3, 4],
    [9, 6, 5, 6, 11],
    [2, 8, 7, 8, 7],
    [9, 10, 5, 10, 11]]

theorem a_5 : a 5 = 13 :=
  a_eq_of_cert (ofRows 5 rows5) (by decide +kernel) (by decide +kernel)
    (labOf 5 labels5) (by decide +kernel) (by decide +kernel)

/-- `a 6 = 20`: the witness `rows6` and the labelling `labels6`. -/
def rows6 : List ℕ :=
  [0b110011,
    0b110011,
    0b001100,
    0b001100,
    0b110011,
    0b110011]

def labels6 : List (List ℕ) :=
  [[16, 0, 1, 0, 1, 2],
    [3, 17, 3, 4, 18, 4],
    [9, 10, 5, 6, 5, 2],
    [7, 13, 7, 8, 14, 15],
    [9, 10, 11, 6, 11, 19],
    [12, 13, 12, 8, 14, 15]]

theorem a_6 : a 6 = 20 :=
  a_eq_of_cert (ofRows 6 rows6) (by decide +kernel) (by decide +kernel)
    (labOf 6 labels6) (by decide +kernel) (by decide +kernel)

/-- `a 7 = 25`: the witness `rows7` and the labelling `labels7`. -/
def rows7 : List ℕ :=
  [0b1001100,
    0b1100110,
    0b0110011,
    0b0011001,
    0b1001100,
    0b1100110,
    0b0110011]

def labels7 : List (List ℕ) :=
  [[0, 1, 2, 1, 2, 3, 9],
    [4, 24, 4, 6, 5, 6, 5],
    [0, 14, 7, 8, 7, 3, 9],
    [10, 18, 10, 11, 19, 20, 12],
    [13, 14, 13, 8, 15, 16, 23],
    [17, 18, 17, 11, 19, 20, 12],
    [21, 22, 21, 22, 15, 16, 23]]

theorem a_7 : a 7 = 25 :=
  a_eq_of_cert (ofRows 7 rows7) (by decide +kernel) (by decide +kernel)
    (labOf 7 labels7) (by decide +kernel) (by decide +kernel)

/-- `a 8 = 32`: the witness `rows8` and the labelling `labels8`. -/
def rows8 : List ℕ :=
  [0b11001100,
    0b11001100,
    0b00110011,
    0b00110011,
    0b11001100,
    0b11001100,
    0b00110011,
    0b00110011]

def labels8 : List (List ℕ) :=
  [[0, 1, 8, 3, 2, 3, 2, 11],
    [4, 5, 4, 13, 6, 7, 14, 15],
    [0, 1, 8, 9, 18, 9, 10, 11],
    [20, 5, 12, 13, 6, 7, 14, 15],
    [16, 17, 24, 17, 18, 19, 10, 27],
    [20, 21, 12, 29, 22, 23, 30, 31],
    [16, 25, 24, 25, 26, 19, 26, 27],
    [28, 21, 28, 29, 22, 23, 30, 31]]

theorem a_8 : a 8 = 32 :=
  a_eq_of_cert (ofRows 8 rows8) (by decide +kernel) (by decide +kernel)
    (labOf 8 labels8) (by decide +kernel) (by decide +kernel)

/-- `a 9 = 41`: the witness `rows9` and the labelling `labels9`. -/
def rows9 : List ℕ :=
  [0b110011001,
    0b011001100,
    0b001100110,
    0b100110011,
    0b110011001,
    0b011001100,
    0b001100110,
    0b100110011,
    0b110011001]

def labels9 : List (List ℕ) :=
  [[0, 1, 0, 3, 2, 3, 4, 12, 4],
    [5, 6, 5, 14, 7, 8, 15, 16, 9],
    [17, 1, 10, 11, 2, 11, 40, 12, 21],
    [22, 6, 13, 14, 7, 8, 15, 16, 9],
    [17, 18, 10, 18, 19, 20, 19, 20, 21],
    [22, 23, 13, 32, 24, 25, 33, 34, 26],
    [35, 36, 27, 28, 37, 38, 29, 30, 39],
    [31, 23, 31, 32, 24, 25, 33, 34, 26],
    [35, 36, 27, 28, 37, 38, 29, 30, 39]]

theorem a_9 : a 9 = 41 :=
  a_eq_of_cert (ofRows 9 rows9) (by decide +kernel) (by decide +kernel)
    (labOf 9 labels9) (by decide +kernel) (by decide +kernel)

/-- `a 10 = 52`: the witness `rows10` and the labelling `labels10`. -/
def rows10 : List ℕ :=
  [0b1100110011,
    0b1100110011,
    0b0011001100,
    0b0011001100,
    0b1100110011,
    0b1100110011,
    0b0011001100,
    0b0011001100,
    0b1100110011,
    0b1100110011]

def labels10 : List (List ℕ) :=
  [[0, 1, 0, 3, 2, 3, 4, 5, 4, 5],
    [6, 48, 6, 13, 49, 7, 14, 15, 8, 9],
    [16, 1, 10, 50, 2, 19, 51, 11, 20, 21],
    [22, 23, 12, 13, 24, 7, 14, 15, 8, 9],
    [16, 17, 10, 17, 18, 19, 18, 11, 20, 21],
    [22, 23, 12, 25, 24, 25, 26, 35, 26, 27],
    [36, 37, 28, 29, 38, 39, 30, 31, 40, 41],
    [42, 43, 32, 33, 44, 45, 34, 35, 46, 27],
    [36, 37, 28, 29, 38, 39, 30, 31, 40, 41],
    [42, 43, 32, 33, 44, 45, 34, 47, 46, 47]]

theorem a_10 : a 10 = 52 :=
  a_eq_of_cert (ofRows 10 rows10) (by decide +kernel) (by decide +kernel)
    (labOf 10 labels10) (by decide +kernel) (by decide +kernel)

/-- Independent cross-check of the first three values by brute force over all subsets of the
board, straight from the definition of `a` (no certificates). -/
theorem a_small : [a 1, a 2, a 3] = [1, 4, 5] := by
  decide +kernel

/-- The definition reproduces the first 10 terms listed in OEIS (all listed terms). Each value is
proved by `a_eq_of_cert` from certificates whose side conditions are kernel-checked
(`decide +kernel`). -/
theorem a_data : (List.range 10).map (fun i => a (i + 1)) =
    [1, 4, 5, 8, 13, 20, 25, 32, 41, 52] := by
  show [a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10] = _
  rw [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10]

/-- Conjecture (Yang Hong, A348484): for every `n ≥ 1`, `a(n) = n²/2` if `n ≡ 0 (mod 4)`,
`a(n) = (n² + 1)/2` if `n ≡ 1` or `3 (mod 4)`, and `a(n) = n²/2 + 2` if `n ≡ 2 (mod 4)`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (n % 4 = 0 → a n = n ^ 2 / 2) ∧
    (n % 4 = 1 ∨ n % 4 = 3 → a n = (n ^ 2 + 1) / 2) ∧
    (n % 4 = 2 → a n = n ^ 2 / 2 + 2)

end Math0.Statements.A348484
