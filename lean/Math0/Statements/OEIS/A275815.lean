/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A275815: maximum total number of moves of same-colored queens on an `n × n` board

Source: https://oeis.org/A275815, _Alec Jones_, Nov 16 2016. Verbatim (FORMULA):
> Conjecture: a(n) = 8(n-2)^2 for n >= 6. - _Alec Jones_, Nov 16 2016

The entry (_Peter Kagey_, Nov 14 2016, offset `1`) is named "Maximum total number of possible
moves that any number of queens of the same color can make on an n X n chessboard."

## Encoding

* *Board and placements.* The squares of the `n × n` board are the pairs `(i, j)` of natural
  numbers with `i, j < n` (`board n`). A placement of any number of queens (possibly none) is a
  subset `S ⊆ board n`, one queen on each square of `S`.
* *Moves.* All queens have the same color, so a queen can neither capture nor jump over another
  queen: it moves to an *empty* square of the board along one of its eight directions, and every
  square passed on the way must be empty too. For a queen on `p` and a direction `d ∈ ℤ²`, the
  queen can stop on `p + k • d` (`k ≥ 1`) iff all of `p + d, …, p + k • d` are empty squares of
  the board (`isEmptySquare`). The number of such `k` is the length of the longest initial run of
  empty squares among `p + t • d`, `t = 1, …, n` (`rayMoves`; the square `p + n • d` is never on
  the board for `d ≠ 0`). Distinct pairs `(d, k)` give distinct target squares, so `rayMoves`
  summed over the eight queen directions (`queenDirs`) is the number of moves of that queen.
  `totalMoves n S` is the total number of moves, summed over all queens of `S`. This reading
  reproduces the entry's example for `n = 3` (`example3`: queens on `A3, A2, B1, C3` make
  `3 + 4 + 5 + 5 = 17` moves).
* *The sequence.* `a n` is the maximum of `totalMoves n` over all placements `S ⊆ board n`
  (offset `1`; `a 0 = 0` is a harmless extra value). It is computable, by exhaustive search over
  the `2 ^ (n * n)` placements; the definition does not use the conjectured formula.
* *The conjecture.* `statement`: for every `n ≥ 6`, `a n = 8 * (n - 2) ^ 2` (natural-number
  subtraction, exact since `n ≥ 6`). No other hypotheses.

## Data checks

* `a_data`: the kernel computes `a 1, a 2, a 3 = 0, 4, 17`, the first three listed terms. The
  definition is an exhaustive search over `2 ^ (n * n)` placements, so `n = 4` (`65536`
  placements) is already far beyond what the kernel does in about a minute.
* `a_ge_data`: lower bounds for the listed terms with `4 ≤ n ≤ 12`. For each such `n` an
  explicit placement (search results for `n = 4, 5`; the `4n - 4` border squares for `n ≥ 6`, as
  in the entry's FORMULA section) has, by kernel computation, exactly the listed number of moves
  (`witness_spec`). Hence `a n ≥ A275815(n)` for `4 ≤ n ≤ 12`. The range is sized to the kernel
  budget: the checks in this file take about a minute of kernel time in total, and each further
  `n ≥ 13` would add at least about 15 seconds. (Outside Lean, the border placements were also
  checked to attain every listed term up to `a(32) = 7200`.)
-/

namespace Math0.Statements.A275815

/-- The squares of the `n × n` board: pairs `(i, j)` of natural numbers with `i, j < n`. -/
def board (n : ℕ) : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n

/-- The point `(x, y) ∈ ℤ²` is a square of the `n × n` board that carries no queen of the
placement `S`. -/
def isEmptySquare (n : ℕ) (S : Finset (ℕ × ℕ)) (x y : ℤ) : Bool :=
  decide (0 ≤ x ∧ x < n ∧ 0 ≤ y ∧ y < n ∧ (x.toNat, y.toNat) ∉ S)

/-- The number of moves of a queen on the square `p` in the direction `d`: the number of `k ≥ 1`
such that `p + d, p + 2 • d, …, p + k • d` are all empty squares of the board, i.e. the length of
the longest initial segment of `t = 1, 2, …, n` for which `p + t • d` is an empty square. -/
def rayMoves (n : ℕ) (S : Finset (ℕ × ℕ)) (p : ℕ × ℕ) (d : ℤ × ℤ) : ℕ :=
  ((List.range' 1 n).takeWhile fun t =>
    isEmptySquare n S (p.1 + t * d.1) (p.2 + t * d.2)).length

/-- The eight directions of a queen. -/
def queenDirs : List (ℤ × ℤ) :=
  [(1, 1), (1, -1), (-1, 1), (-1, -1), (1, 0), (-1, 0), (0, 1), (0, -1)]

/-- The total number of moves that the queens of the placement `S` (all of the same color) can
make on the `n × n` board. -/
def totalMoves (n : ℕ) (S : Finset (ℕ × ℕ)) : ℕ :=
  ∑ p ∈ S, (queenDirs.map (rayMoves n S p)).sum

/-- A275815: the maximum total number of possible moves that any number of queens of the same
color can make on an `n × n` chessboard. -/
def a (n : ℕ) : ℕ := (board n).powerset.sup (totalMoves n)

/-- The definition reproduces the first terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 3).map (fun i => a (i + 1)) = [0, 4, 17] := by
  decide +kernel

/-- The entry's example for `n = 3`: queens on `A3, A2, B1, C3`, written as `(column, row - 1)`,
make `3 + 4 + 5 + 5 = 17` moves. -/
theorem example3 :
    ([(0, 2), (0, 1), (1, 0), (2, 2)].map fun p =>
        (queenDirs.map (rayMoves 3 {(0, 2), (0, 1), (1, 0), (2, 2)} p)).sum) = [3, 4, 5, 5] ∧
      totalMoves 3 {(0, 2), (0, 1), (1, 0), (2, 2)} = 17 := by
  decide +kernel

/-! ### Lower bounds for further listed terms -/

/-- The `4n - 4` squares on the border of the `n × n` board. -/
def border (n : ℕ) : Finset (ℕ × ℕ) :=
  (board n).filter fun p => p.1 = 0 ∨ p.1 = n - 1 ∨ p.2 = 0 ∨ p.2 = n - 1

/-- Queen placements attaining the listed values for `4 ≤ n ≤ 12`. -/
def witness : ℕ → Finset (ℕ × ℕ)
  | 4 => {(0, 0), (0, 2), (0, 3), (1, 0), (2, 3), (3, 1)}
  | 5 => {(0, 1), (0, 2), (0, 3), (1, 0), (1, 4), (2, 2), (3, 0), (3, 4), (4, 1), (4, 2), (4, 3)}
  | n => border n

theorem witness_spec : ∀ i < 9, witness (i + 4) ⊆ board (i + 4) ∧
    totalMoves (i + 4) (witness (i + 4)) =
      [40, 76, 128, 200, 288, 392, 512, 648, 800].getD i 0 := by
  decide +kernel

/-- The listed terms `a(4), …, a(12)` are lower bounds for `a`. -/
theorem a_ge_data :
    ∀ i < 9, [40, 76, 128, 200, 288, 392, 512, 648, 800].getD i 0 ≤ a (i + 4) := by
  intro i hi
  obtain ⟨hS, hv⟩ := witness_spec i hi
  exact hv ▸ Finset.le_sup (f := totalMoves (i + 4)) (Finset.mem_powerset.mpr hS)

/-- Alec Jones's conjecture: for every `n ≥ 6`, the maximum total number of moves that any number
of same-colored queens can make on an `n × n` chessboard is `8 (n - 2) ^ 2`. -/
def statement : Prop := ∀ n : ℕ, 6 ≤ n → a n = 8 * (n - 2) ^ 2

end Math0.Statements.A275815
