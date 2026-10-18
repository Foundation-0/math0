/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A394981: tilings of the smallest-perimeter rectangle by the bars `1 × 1, …, 1 × n`

Source: https://oeis.org/A394981, _Gary Yane_, Apr 08 2026 (a(1)-a(2) corrected by
_Pontus von Brömssen_, May 13 2026). Verbatim (FORMULA section, unattributed):
> Conjecture: If n is odd, then a(n+1) = 4*a(n).

The entry's definition: "Given a set of n rectangular tiles, {1 X 1, 1 X 2, 1 X 3, 1 X 4, ..., 1 X n},
then a(n) is the number of tilings up to symmetry of the rectangle having smallest possible
perimeter with area n*(n+1)/2 using all n tiles." Its comment makes the rectangle precise: "So,
when n=8 the area is 36 and we are only counting the number of ways to use the tiles to make a
4 X 9 rectangle not 1 X 36, 2 X 18, nor 3 X 12 rectangles. That is, the short side of the rectangle
has length floor((n+1)/2)." Offset `1`.

## Encoding

* The rectangle has `r = rows n = ⌊(n + 1) / 2⌋` rows (the short side, as in the comment) and
  `c = cols n = (n (n + 1) / 2) / r` columns, i.e. area `n (n + 1) / 2`; this is `r × n` for odd
  `n` and `r × (n + 1)` for even `n` (`rect_data`). It is the rectangle of area `n (n + 1) / 2`
  with smallest perimeter among those into which the `1 × n` tile fits (the entry's `n = 8`
  example: `4 × 9`, not the `6 × 6` square).
* Cell `(i, j)` (`i < r`, `j < c`) has index `i * c + j`; a set of cells is a bitmask (bit `p` set
  iff cell `p` is in the set).
* A placement of the `1 × k` tile is the set of cells it covers: `k` consecutive cells of a row
  (horizontal) or of a column (vertical). For `k = 1` both orientations cover the same single
  cell and are the same placement. A tiling assigns to every tile `k = 1, …, n` a placement inside
  the rectangle, the placements being pairwise disjoint and covering the rectangle. As the tiles
  have pairwise different lengths, this is the same as a partition of the rectangle into one bar
  of each length `1, …, n`.
* Tilings are enumerated by the standard exact-cover recursion `search`: the first uncovered cell
  `q` (in row-major order) must be the first cell of the tile covering it (all earlier cells are
  already covered), so that tile is placed horizontally from `q` or, if `k ≥ 2`, vertically from
  `q`. Every tiling is reached by exactly one branch (its tiles are placed in the row-major order
  of their first cells), and every completed branch is a tiling.
* "Up to symmetry": the symmetry group `G` of the rectangle acts on cells, hence on tilings (tile
  `k` of `g • T` covers the `g`-image of the cells of tile `k` of `T`). For a non-square rectangle
  `G` consists of the identity, the two reflections and the half-turn; for a square (here only
  `n = 1`, the `1 × 1` square) all 8 symmetries. `a n` is the number of orbits, computed by
  Burnside's lemma (orbit-stabilizer: the tilings of one orbit have stabilizer sizes summing to
  `|G|`) as `(∑_T |Stab T|) / |G|`, where `stabCount` counts the symmetries mapping every tile of
  `T` onto itself.
* For speed in the kernel, `mask` and `firstFree` are written with the recursors and the bit
  operations with `Nat.land`/`Nat.lor`/`Nat.shiftRight`/`Nat.beq`; they compute exactly what their
  docstrings say.

## Reading of the conjecture

With offset `1`, "if n is odd" literally includes `n = 1`, but the entry's own (corrected) data have
`a(1) = a(2) = 1`, so the literal reading fails at `n = 1` (`literal_fails_at_one`), the degenerate
case of the `1 × 1` square tiled by a single tile. The conjecture is read as the pattern it
describes in the data: `a(n + 1) = 4 a(n)` for every odd `n ≥ 3` (it holds for all listed pairs
`n = 3, 5, …, 19`). `statement` is this reading, with no other hypotheses.
-/

namespace Math0.Statements.A394981

/-- The number of rows (the short side) of the rectangle for `n` tiles: `⌊(n + 1) / 2⌋`. -/
def rows (n : ℕ) : ℕ := (n + 1) / 2

/-- The number of columns (the long side) of the rectangle for `n` tiles: the area
`n (n + 1) / 2` divided by `rows n` (this is `n` for odd `n` and `n + 1` for even `n`). -/
def cols (n : ℕ) : ℕ := n * (n + 1) / 2 / rows n

/-- The rectangles for `n = 1, …, 20`: `rows n × cols n`. -/
theorem rect_data : (List.range 20).map (fun i => (rows (i + 1), cols (i + 1))) =
    [(1, 1), (1, 3), (2, 3), (2, 5), (3, 5), (3, 7), (4, 7), (4, 9), (5, 9), (5, 11), (6, 11),
      (6, 13), (7, 13), (7, 15), (8, 15), (8, 17), (9, 17), (9, 19), (10, 19), (10, 21)] := by
  decide +kernel

/-- The bitmask of the set of cells with the given indices: `∑ 2 ^ p` over the (distinct) cells. -/
def mask (cells : List ℕ) : ℕ := cells.rec 0 fun p _ m => Nat.lor (2 ^ p) m

/-- Whether cell `p` is not in the set `used` (bit `p` of `used` is `0`). -/
def isFree (used p : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight used p) 1) 0

/-- `firstFree used fuel p` is the least cell index `q ≥ p` not in `used` among
`p, p + 1, …, p + fuel - 1` (and `p + fuel` if there is none). -/
def firstFree (used fuel p : ℕ) : ℕ :=
  fuel.rec (fun p => p) (fun _ ih p => if isFree used p then p else ih (p + 1)) p

/-- The placements of the `1 × k` tile (`k ≥ 1`) in the `r × c` rectangle whose first cell (in
row-major order) is cell `q`, each as its list of cells: horizontal, cells `q, q + 1, …, q + k - 1`,
if they lie in the row of `q`; vertical, cells `q, q + c, …, q + (k - 1) c`, if they lie in the
rectangle, and only for `k ≥ 2` (for `k = 1` it would be the same placement as the horizontal
one). -/
def barsAt (r c q k : ℕ) : List (List ℕ) :=
  (if q / c < r ∧ q % c + k ≤ c then [(List.range k).map (q + ·)] else []) ++
  (if 2 ≤ k ∧ q / c + k ≤ r then [(List.range k).map fun t => q + t * c] else [])

/-- `search r c f m used p unused acc` is the sum of `f T` over all tilings `T` of the `r × c`
rectangle that extend the partial tiling `acc` (a list of placed tiles `(k, cells)`), whose cells
form the set `used` and contain all cells with index `< p`, by the `m` tiles `unused`. The tilings
are given as lists of pairs `(k, cells of the 1 × k tile)`. At each step the first uncovered cell
`q` is covered by some unused tile `k` placed with first cell `q`; a branch is complete when all
tiles are placed and all `r * c` cells are covered. -/
def search (r c : ℕ) (f : List (ℕ × List ℕ) → ℕ) :
    ℕ → ℕ → ℕ → List ℕ → List (ℕ × List ℕ) → ℕ
  | 0, used, _, _, acc => if used = 2 ^ (r * c) - 1 then f acc else 0
  | m + 1, used, p, unused, acc =>
    let q := firstFree used (r * c) p
    (unused.map fun k =>
      ((barsAt r c q k).map fun P =>
        let mP := mask P
        if Nat.land mP used = 0 then
          search r c f m (Nat.lor used mP) q (unused.erase k) ((k, P) :: acc)
        else 0).sum).sum

/-- The symmetries of the `r × c` rectangle, as maps on cell coordinates `(i, j)`: the identity,
the reflections in the horizontal and in the vertical axis, and the half-turn; if the rectangle is
a square (`r = c`), also the reflections in the two diagonals and the two quarter-turns. -/
def symmetries (r c : ℕ) : List (ℕ × ℕ → ℕ × ℕ) :=
  [fun p => p, fun p => (r - 1 - p.1, p.2), fun p => (p.1, c - 1 - p.2),
    fun p => (r - 1 - p.1, c - 1 - p.2)] ++
  (if r = c then
    [fun p => (p.2, p.1), fun p => (c - 1 - p.2, r - 1 - p.1), fun p => (p.2, r - 1 - p.1),
      fun p => (c - 1 - p.2, p.1)]
  else [])

/-- The action of a symmetry `g` on cell indices of a rectangle with `c` columns. -/
def act (c : ℕ) (g : ℕ × ℕ → ℕ × ℕ) (p : ℕ) : ℕ :=
  let q := g (p / c, p % c)
  q.1 * c + q.2

/-- The size of the stabilizer of the tiling `T` (a list of tiles `(k, cells)`) of the `r × c`
rectangle: the number of symmetries mapping the cells of every tile of `T` onto themselves. -/
def stabCount (r c : ℕ) (T : List (ℕ × List ℕ)) : ℕ :=
  ((symmetries r c).filter fun g => T.all fun t => mask (t.2.map (act c g)) = mask t.2).length

/-- A394981: the number of tilings, up to the symmetries of the rectangle, of the
`rows n × cols n` rectangle (area `n (n + 1) / 2`, smallest perimeter) by the `n` tiles
`1 × 1, 1 × 2, …, 1 × n`, each used once. Computed by Burnside's lemma as the sum of the stabilizer
sizes over all tilings, divided by the order of the symmetry group. -/
def a (n : ℕ) : ℕ :=
  search (rows n) (cols n) (stabCount (rows n) (cols n)) n 0 0 ((List.range n).map (· + 1)) [] /
    (symmetries (rows n) (cols n)).length

end Math0.Statements.A394981
