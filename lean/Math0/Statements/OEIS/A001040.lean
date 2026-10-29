/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A001040: Kurkov's rook-tour interpretation of `2 · n! · a(n)`

Source: https://oeis.org/A001040, Mikhail Kurkov, Nov 19 2019 (COMMENTS section). Verbatim:
> Conjecture: 2*n!*a(n) is the number of open tours by a rook on an (n X 2) chessboard which
> ends at the opposite line of length n.

The sequence (offset `0`) is "a(n+1) = n*a(n) + a(n-1) with a(0)=0, a(1)=1."

## Encoding

* `a` is the defining recursion `a 0 = 0`, `a 1 = 1`, `a (n + 2) = (n + 1) * a (n + 1) + a n`
  (the OEIS recursion `a(m+1) = m*a(m) + a(m-1)` with `m = n + 1 ≥ 1`). `a_data` checks all 24
  listed terms `a 0, …, a 23`.
* The `n × 2` board is `Fin n × Fin 2`: the square `(i, c)` is the `i`-th square of the line `c`
  of length `n` (there are two such lines, `c = 0` and `c = 1`; the `n` short rows of length `2`
  are the sets `{(i, 0), (i, 1)}`).
* A rook move (`RookMove`) goes between two different squares in the same row or in the same
  line; the rook may move any distance and pass over squares (visited or not). This is the
  adjacency of the rook graph `K_n □ K_2` (`rookMove_iff`, stated with Mathlib's `boxProd`).
* An open tour (`IsOpenTour n l`) is a sequence `l` of squares that visits every square exactly
  once (`l.Nodup` and every square is in `l`) and in which consecutive squares are a rook move
  apart (`l.IsChain RookMove`), i.e. a Hamiltonian path of the rook graph, read with its
  direction (a tour and its reversal are different tours). It "ends at the opposite line"
  (`EndsOnOppositeLine l`) when its first and last squares lie in different lines of length `n`.
* Reading choices, both forced by the listed data at `n = 1` (where `2 · 1! · a(1) = 2`): on the
  `1 × 2` board the only open tours are `(0,0) → (0,1)` and `(0,1) → (0,0)`, so tours are counted
  as directed sequences (undirected paths would give `1`), and "open" means "not required to
  return to its start", not "its ends are not a rook move apart" (that reading would give `0`).
* The count is the `Set.ncard` of the set of such lists. The set is finite; `ncard_eq_card_tours`
  identifies it with the computable `Finset` `tours n` (orderings of the squares, filtered), and
  `tours_card_small` kernel-checks the counts `2, 4, 36, 480` for `n = 1, 2, 3, 4`, which equal
  `2 · n! · a(n)` (these values only test the encoding; they are not part of the statement).
* The conjecture is stated for every board size `n ≥ 1`. (For `n = 0` both sides are `0` under
  this encoding, see `tours_zero`, so nothing would change if `n = 0` were included.)
-/

namespace Math0.Statements.A001040

open Nat

/-- A001040: `a(0) = 0`, `a(1) = 1`, `a(n+1) = n*a(n) + a(n-1)`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 1) * a (n + 1) + a n

/-- The definition reproduces the first terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 24).map (fun i => a (i + 0)) =
    [0, 1, 1, 3, 10, 43, 225, 1393, 9976, 81201, 740785, 7489051, 83120346, 1004933203,
     13147251985, 185066460993, 2789144166880, 44811373131073, 764582487395121,
     13807296146243251, 263103209266016890, 5275871481466581051, 111056404320064218961,
     2448516766522879398193] := by
  decide +kernel

/-- A rook move on the `n × 2` board `Fin n × Fin 2` (square `(i, c)` = `i`-th square of the
line `c`): between two different squares in the same row (`i`) or in the same line (`c`). -/
def RookMove {n : ℕ} (p q : Fin n × Fin 2) : Prop :=
  p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2)

instance {n : ℕ} : DecidableRel (@RookMove n) := fun p q => by
  unfold RookMove; infer_instance

/-- Rook moves are the edges of the rook graph `K_n □ K_2`. -/
theorem rookMove_iff {n : ℕ} (p q : Fin n × Fin 2) :
    RookMove p q ↔ ((⊤ : SimpleGraph (Fin n)) □ (⊤ : SimpleGraph (Fin 2))).Adj p q := by
  obtain ⟨i, c⟩ := p
  obtain ⟨j, d⟩ := q
  simp only [RookMove, SimpleGraph.boxProd_adj, SimpleGraph.top_adj, ne_eq, Prod.mk.injEq]
  tauto

/-- An open rook tour of the `n × 2` board: a sequence of squares visiting every square exactly
once, consecutive squares being a rook move apart. -/
def IsOpenTour (n : ℕ) (l : List (Fin n × Fin 2)) : Prop :=
  l.Nodup ∧ (∀ s, s ∈ l) ∧ l.IsChain RookMove

/-- The sequence starts and ends in different lines of length `n`. -/
def EndsOnOppositeLine {n : ℕ} (l : List (Fin n × Fin 2)) : Prop :=
  ∃ s ∈ l.head?, ∃ t ∈ l.getLast?, s.2 ≠ t.2

instance {n : ℕ} (l : List (Fin n × Fin 2)) : Decidable (EndsOnOppositeLine l) := by
  unfold EndsOnOppositeLine; infer_instance

/-- Kurkov's conjecture: for every `n ≥ 1`, the number of open rook tours of the `n × 2` board
that end on the line of length `n` opposite to the one they start on is `2 · n! · a(n)`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    {l : List (Fin n × Fin 2) | IsOpenTour n l ∧ EndsOnOppositeLine l}.ncard = 2 * n ! * a n

/-! ## Sanity checks of the encoding (not part of the statement) -/

/-- The `2n` squares of the board, each once. -/
def squares (n : ℕ) : List (Fin n × Fin 2) := List.finRange n ×ˢ List.finRange 2

theorem squares_nodup (n : ℕ) : (squares n).Nodup :=
  (List.nodup_finRange n).product (List.nodup_finRange 2)

theorem mem_squares {n : ℕ} (s : Fin n × Fin 2) : s ∈ squares n := by
  obtain ⟨i, c⟩ := s
  simp [squares]

/-- The open tours ending on the opposite line, enumerated as the orderings of `squares n`
(`List.permutations'`) that pass the two tests. -/
def tours (n : ℕ) : Finset (List (Fin n × Fin 2)) :=
  ⟨((squares n).permutations'.filter fun l => l.IsChain RookMove ∧ EndsOnOppositeLine l : List _),
    ((List.permutations_perm_permutations' _).nodup_iff.mp
      (List.nodup_permutations _ (squares_nodup n))).filter _⟩

theorem mem_tours {n : ℕ} {l : List (Fin n × Fin 2)} :
    l ∈ tours n ↔ IsOpenTour n l ∧ EndsOnOppositeLine l := by
  have key : List.Perm l (squares n) ↔ l.Nodup ∧ ∀ s, s ∈ l := by
    constructor
    · intro h
      exact ⟨h.nodup_iff.mpr (squares_nodup n), fun s => h.mem_iff.mpr (mem_squares s)⟩
    · rintro ⟨hl, hs⟩
      exact (List.perm_ext_iff_of_nodup hl (squares_nodup n)).mpr
        fun s => ⟨fun _ => mem_squares s, fun _ => hs s⟩
  rw [tours, Finset.mem_def]
  simp only [Multiset.mem_coe, List.mem_filter, List.mem_permutations', key, decide_eq_true_eq,
    IsOpenTour]
  tauto

/-- The set counted in `statement` is the finite set `tours n`. -/
theorem ncard_eq_card_tours (n : ℕ) :
    {l : List (Fin n × Fin 2) | IsOpenTour n l ∧ EndsOnOppositeLine l}.ncard = (tours n).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext l
  simp [mem_tours]

/-- The counts for `n = 1, 2, 3, 4` are `2, 4, 36, 480` (kernel-checked), and these are
`2 · n! · a(n)`. -/
theorem tours_card_small :
    (List.range 4).map (fun i => (tours (i + 1)).card) = [2, 4, 36, 480] ∧
      (List.range 4).map (fun i => 2 * (i + 1)! * a (i + 1)) = [2, 4, 36, 480] := by
  decide +kernel

/-- On the empty board there is no tour ending on the opposite line (and `2 · 0! · a(0) = 0`). -/
theorem tours_zero : (tours 0).card = 0 := by decide +kernel

end Math0.Statements.A001040
