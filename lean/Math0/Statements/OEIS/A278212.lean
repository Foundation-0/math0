/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A278212: maximum total number of moves of same-colored bishops on an `n × n` board

Source: https://oeis.org/A278212, _Peter Kagey_, Nov 24 2016. Verbatim (COMMENTS):
> Conjecture: a(n) = floor(A275815(n)/2). - _Peter Kagey_, Nov 24 2016

The entry's name is "Maximum total number of possible moves that any number of bishops of the
same color can make on an n X n chessboard." (offset `1`). A275815 (offset `1`) is "Maximum total
number of possible moves that any number of queens of the same color can make on an n X n
chessboard."

## Encoding

* *Board and placements.* The squares of the `n × n` board are the pairs `(i, j)` of natural
  numbers with `i, j < n` (`board n`). A placement of any number of pieces (possibly none) is a
  subset `S ⊆ board n`, one piece on each square of `S`.
* *Moves.* All pieces have the same color, so a piece can neither capture nor jump over another
  piece: it moves to an *empty* square of the board along one of its directions, and every
  square passed on the way must be empty too. For a piece on `p` and a direction `d ∈ ℤ²`, the
  piece can stop on `p + k • d` (`k ≥ 1`) iff all of `p + d, …, p + k • d` are empty squares of
  the board (`isEmptySquare`). The number of such `k` is the length of the longest initial run of
  empty squares among `p + t • d`, `t = 1, …, n` (`rayMoves`; the square `p + n • d` is never on
  the board for `d ≠ 0`). Distinct pairs `(d, k)` give distinct target squares.
  Bishops move in the four diagonal directions `(±1, ±1)` (`bishopDirs`); queens in these and
  the four orthogonal directions `(±1, 0)`, `(0, ±1)` (`queenDirs`). `totalMoves dirs n S` is
  the total number of moves, summed over all pieces of `S`.
  "Same color" refers to the pieces (one side), not to the color of their squares: the entry's
  example for `n = 5` has bishops on squares of both colors (`bishopWitness 5` below).
* *The sequences.* `a n` (A278212) and `queenMax n` (A275815) are the maxima of `totalMoves` over
  all placements `S ⊆ board n`, for bishops and for queens respectively. Both are computable (by
  exhaustive search over the `2 ^ (n * n)` placements).
* *The conjecture.* `statement`: for every `n ≥ 1` (the common offset of both sequences),
  `a n = queenMax n / 2`, where `/` is natural-number division, i.e. `floor`.

## Data checks

* `a_data`, `queenMax_data`: the kernel computes `a 1, a 2, a 3 = 0, 2, 8` and
  `queenMax 1, queenMax 2, queenMax 3 = 0, 4, 17`, the first three listed terms of A278212 and of
  A275815. The definition is an exhaustive search over `2 ^ (n * n)` placements, so `n = 4`
  (`65536` placements) is already beyond what the kernel does in about a minute.
* `a_ge_data`, `queenMax_ge_data`: lower bounds for the listed terms with `4 ≤ n ≤ 10`. For each
  such `n` an explicit placement (the entry's example for bishops with `n = 5`, search results
  for `n = 4` and for queens with `n = 5`, the `4n - 4` border squares for `n ≥ 6` as in the
  entry's FORMULA section) has, by kernel computation, exactly the listed number of moves
  (`bishopWitness_spec`, `queenWitness_spec`). Hence `a n ≥ A278212(n)` and
  `queenMax n ≥ A275815(n)` for `4 ≤ n ≤ 10`.
-/

namespace Math0.Statements.A278212

/-- The squares of the `n × n` board: pairs `(i, j)` of natural numbers with `i, j < n`. -/
def board (n : ℕ) : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n

/-- The point `(x, y) ∈ ℤ²` is a square of the `n × n` board that carries no piece of the
placement `S`. -/
def isEmptySquare (n : ℕ) (S : Finset (ℕ × ℕ)) (x y : ℤ) : Bool :=
  decide (0 ≤ x ∧ x < n ∧ 0 ≤ y ∧ y < n ∧ (x.toNat, y.toNat) ∉ S)

/-- The number of moves of a piece on the square `p` in the direction `d`: the number of `k ≥ 1`
such that `p + d, p + 2 • d, …, p + k • d` are all empty squares of the board, i.e. the length of
the longest initial segment of `t = 1, 2, …, n` for which `p + t • d` is an empty square. -/
def rayMoves (n : ℕ) (S : Finset (ℕ × ℕ)) (p : ℕ × ℕ) (d : ℤ × ℤ) : ℕ :=
  ((List.range' 1 n).takeWhile fun t =>
    isEmptySquare n S (p.1 + t * d.1) (p.2 + t * d.2)).length

/-- The four directions of a bishop. -/
def bishopDirs : List (ℤ × ℤ) := [(1, 1), (1, -1), (-1, 1), (-1, -1)]

/-- The eight directions of a queen. -/
def queenDirs : List (ℤ × ℤ) :=
  [(1, 1), (1, -1), (-1, 1), (-1, -1), (1, 0), (-1, 0), (0, 1), (0, -1)]

/-- The total number of moves that the pieces of the placement `S` (all of the same color, each
moving in the directions `dirs`) can make on the `n × n` board. -/
def totalMoves (dirs : List (ℤ × ℤ)) (n : ℕ) (S : Finset (ℕ × ℕ)) : ℕ :=
  ∑ p ∈ S, (dirs.map (rayMoves n S p)).sum

/-- A278212: the maximum total number of possible moves that any number of bishops of the same
color can make on an `n × n` chessboard. -/
def a (n : ℕ) : ℕ := (board n).powerset.sup (totalMoves bishopDirs n)

/-- A275815: the maximum total number of possible moves that any number of queens of the same
color can make on an `n × n` chessboard. -/
def queenMax (n : ℕ) : ℕ := (board n).powerset.sup (totalMoves queenDirs n)

/-- The definition reproduces the first terms listed in A278212 (kernel-checked). -/
theorem a_data : (List.range 3).map (fun i => a (i + 1)) = [0, 2, 8] := by
  decide +kernel

/-- The definition reproduces the first terms listed in A275815 (kernel-checked). -/
theorem queenMax_data : (List.range 3).map (fun i => queenMax (i + 1)) = [0, 4, 17] := by
  decide +kernel

/-! ### Lower bounds for further listed terms -/

/-- The `4n - 4` squares on the border of the `n × n` board. -/
def border (n : ℕ) : Finset (ℕ × ℕ) :=
  (board n).filter fun p => p.1 = 0 ∨ p.1 = n - 1 ∨ p.2 = 0 ∨ p.2 = n - 1

/-- Bishop placements attaining the listed values for `4 ≤ n ≤ 10`; the one for `n = 5` is the
example in the entry (`(column, row - 1)` for the squares `A5, B5, C5, E5, E4, A3, B3, E3, E2,
A1, B1, C1, E1`). -/
def bishopWitness : ℕ → Finset (ℕ × ℕ)
  | 4 => {(0, 0), (0, 3), (1, 0), (1, 3), (2, 0), (2, 3), (3, 0), (3, 3)}
  | 5 => {(0, 4), (1, 4), (2, 4), (4, 4), (4, 3), (0, 2), (1, 2), (4, 2), (4, 1), (0, 0), (1, 0),
      (2, 0), (4, 0)}
  | n => border n

/-- Queen placements attaining the listed values for `4 ≤ n ≤ 10`. -/
def queenWitness : ℕ → Finset (ℕ × ℕ)
  | 4 => {(0, 0), (0, 2), (0, 3), (1, 0), (2, 3), (3, 1)}
  | 5 => {(0, 1), (0, 2), (0, 3), (1, 0), (1, 4), (2, 2), (3, 0), (3, 4), (4, 1), (4, 2), (4, 3)}
  | n => border n

theorem bishopWitness_spec : ∀ i < 7, bishopWitness (i + 4) ⊆ board (i + 4) ∧
    totalMoves bishopDirs (i + 4) (bishopWitness (i + 4)) =
      [20, 38, 64, 100, 144, 196, 256].getD i 0 := by
  decide +kernel

theorem queenWitness_spec : ∀ i < 7, queenWitness (i + 4) ⊆ board (i + 4) ∧
    totalMoves queenDirs (i + 4) (queenWitness (i + 4)) =
      [40, 76, 128, 200, 288, 392, 512].getD i 0 := by
  decide +kernel

/-- The listed terms `a(4), …, a(10)` of A278212 are lower bounds for `a`. -/
theorem a_ge_data : ∀ i < 7, [20, 38, 64, 100, 144, 196, 256].getD i 0 ≤ a (i + 4) := by
  intro i hi
  obtain ⟨hS, hv⟩ := bishopWitness_spec i hi
  exact hv ▸ Finset.le_sup (f := totalMoves bishopDirs (i + 4)) (Finset.mem_powerset.mpr hS)

/-- The listed terms `a(4), …, a(10)` of A275815 are lower bounds for `queenMax`. -/
theorem queenMax_ge_data :
    ∀ i < 7, [40, 76, 128, 200, 288, 392, 512].getD i 0 ≤ queenMax (i + 4) := by
  intro i hi
  obtain ⟨hS, hv⟩ := queenWitness_spec i hi
  exact hv ▸ Finset.le_sup (f := totalMoves queenDirs (i + 4)) (Finset.mem_powerset.mpr hS)

/-- Kagey's conjecture: for every `n ≥ 1`, A278212(n) = floor(A275815(n) / 2), i.e. the maximum
total number of moves of same-colored bishops on an `n × n` board is the floor of half the
maximum total number of moves of same-colored queens. -/
def statement : Prop := ∀ n : ℕ, 1 ≤ n → a n = queenMax n / 2

end Math0.Statements.A278212
