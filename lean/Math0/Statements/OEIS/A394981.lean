/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A394981: tilings of the smallest-perimeter rectangle by the bars `1 × 1, …, 1 × n`

Source: https://oeis.org/A394981, _Gary Yane_, Apr 08 2026 (a(1)-a(2) corrected by
_Pontus von Brömssen_, May 13 2026). Verbatim (FORMULA section, unattributed):
> Conjecture: If n is odd, then a(n+1) = 4*a(n).

The entry's definition (NAME): "Given a set of n rectangular tiles,
{1 X 1, 1 X 2, 1 X 3, 1 X 4, ..., 1 X n}, then a(n) is the number of tilings up to symmetry of the
rectangle having smallest possible perimeter with area n*(n+1)/2 using all n tiles." Its comment
fixes the rectangle: "The only rectangle we are looking at is the one with the smallest perimeter.
So, when n=8 the area is 36 and we are only counting the number of ways to use the tiles to make a
4 X 9 rectangle not 1 X 36, 2 X 18, nor 3 X 12 rectangles. That is, the short side of the
rectangle has length floor((n+1)/2)." Offset `1`; data `1, 1, 1, 4, 10, 40, 112, 448, 1360, 5440,
…` (20 terms listed).

## Encoding

* **The rectangle** has `r = rows n = ⌊(n + 1) / 2⌋` rows (the short side, as the comment says)
  and `c = cols n = (n (n + 1) / 2) / r` columns, so its area is `n (n + 1) / 2`: it is `r × n`
  for odd `n` and `r × (n + 1)` for even `n` (`rect_data`, `area_data`). This is the rectangle of
  area `n (n + 1) / 2` of smallest perimeter among those the `1 × n` tile fits in (the comment's
  `n = 8` example is `4 × 9`, not the `6 × 6` square, in which `1 × 8` does not fit).
* **Cells and cell sets.** Cell `(i, j)` (`i < r`, `j < c`) has index `p = i * w + j`, where
  `w = c + 1`: each row is followed by one padding index `i * w + c` that is not a cell, so a run of
  consecutive indices inside the rectangle never wraps from one row to the next. A set `S` of
  indices is the bitmask `∑_{p ∈ S} 2 ^ p`; the rectangle is `rectMask r c w`.
* **Placements.** A placement of the `1 × k` tile is the set of cells it covers: the `k` cells
  `q, q + 1, …, q + (k - 1)` (horizontal) or `q, q + w, …, q + (k - 1) w` (vertical) of one row
  or column, all inside the rectangle. Their bitmasks are `barAt (2 ^ q) 1 1 k` and
  `barAt (2 ^ q) 1 w k` (`barAt_eq` gives the sum of powers). For `k = 1` both orientations cover
  the same single cell, i.e. are the same placement, so the vertical one is only used for `k ≥ 2`.
* **Tilings.** A tiling is an assignment, to every tile `k = 1, …, n`, of a placement, the
  placements being pairwise disjoint and covering the rectangle. As the tiles have pairwise
  different lengths, this is the same as a partition of the rectangle into one bar of each length
  `1, …, n`, and different assignments are different tilings.
* **Enumeration.** `search` places the tiles `n, n - 1, …, 1` one after the other, each at every
  placement inside the still free cells `free` (initially the whole rectangle), and at the end
  requires that no free cell is left. So every tiling is produced exactly once (by the branch that
  chooses its own placement for each tile). The possible first cells `q` of tile `k` in the
  direction with step `s` are the set bits of `starts free s k`, whose bit `q` is set iff the cells
  `q, q + s, …, q + (k - 1) s` all lie in `free` (`testBit_starts`); since `free` only contains
  cells of the rectangle and the padding indices `i * w + c` and the indices `≥ r * w` are never
  free, these are exactly the placements of tile `k` inside `free`. `sumBits g N X` is
  `∑ g (2 ^ q)` over the set bits `q` of `X` (it peels off the lowest set bit
  `X - (X &&& (X - 1))` of `X ≠ 0`, and `X &&& (X - 1)` is `X` with that bit cleared; all sets
  here are subsets of `{0, …, N - 1}`, `N = r * w`, so `N` steps suffice).
* **The tiling as a labelling.** Along the way `lab` records the tiling: the field of `n` bits at
  bit position `n * p` holds the length `k` of the tile covering cell `p` (`k ≤ n < 2 ^ n`, and the
  placements are disjoint, so the fields never overflow into each other). `field n lab p` reads it.
* **Up to symmetry.** The symmetry group `G` of the rectangle acts on the cells, hence on tilings
  (tile `k` of `g • T` covers the `g`-image of the cells of tile `k` of `T`). For a non-square
  rectangle `G` consists of the identity, the two reflections in the axes and the half-turn; for a
  square (here only `n = 1`, the `1 × 1` square) all 8 symmetries of the square. `g` fixes `T` iff
  the labelling of `T` is `g`-invariant: `label (g p) = label p` for every cell `p` (`fixes`).
  `a n` is the number of orbits, computed by Burnside's lemma as `(∑_T |Stab T|) / |G|`, where
  `stabCount` is `|Stab T|` (the identity plus the non-identity symmetries `otherSymmetries` that
  fix `T`).
* For speed in the kernel, the recursions are written with the recursors and the bit operations
  with `Nat.land`/`Nat.shiftRight`/`Nat.beq` and `Bool` tests.
* **Data check.** `a_data` checks `a 1, …, a 9` against the listed terms in the kernel (about
  30 s of kernel time and 2.5 GB of memory on our machine; most of it is `a 9`, whose search has
  about 42000 nodes). `a 10` is out of reach of the kernel: its search has about 258000 nodes,
  roughly six times the time and memory of `a 9`. Not kernel-checked, but as further evidence:
  `#eval` of this definition gives `a 10 = 5440` and `a 11 = 17728`, as listed, and an
  independent Python enumeration (tilings as partitions of the rectangle into one bar of each
  length, orbits under the symmetries of the rectangle) gives the listed `a 1, …, a 10`.

## Reading of the conjecture

With offset `1`, "if n is odd" literally includes `n = 1`, but the entry's own (corrected) data have
`a(1) = a(2) = 1` (the `1 × 1` square and the `1 × 3` rectangle each have exactly one tiling), so
the literal reading fails at `n = 1` (`literal_fails_at_one`, kernel-checked). The conjecture is
read as the pattern it describes in the listed data, `a(n + 1) = 4 a(n)` for every odd `n ≥ 3`
(it holds for all listed pairs `n = 3, 5, …, 19`). `statement` is this reading, with no other
hypotheses.
-/

namespace Math0.Statements.A394981

open Finset

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

/-- The rectangle `rows n × cols n` has area `n (n + 1) / 2` for `n = 1, …, 20`. -/
theorem area_data :
    (List.range 20).all (fun i => rows (i + 1) * cols (i + 1) == (i + 1) * (i + 2) / 2) = true := by
  decide +kernel

/-- `barAt x b s k = x ^ b * (2 ^ (b s k) - 1) / (2 ^ (b s) - 1)`; for `x = 2 ^ q` this is
`∑_{t < k} 2 ^ (b (q + t s))` (`barAt_eq`): with `b = 1`, the bitmask of the `k` cells
`q, q + s, …, q + (k - 1) s`; with `b = n`, the same cells in fields of `n` bits. -/
def barAt (x b s k : ℕ) : ℕ := x ^ b * ((2 ^ (b * (s * k)) - 1) / (2 ^ (b * s) - 1))

/-- `barAt (2 ^ q) b s k` is `∑_{t < k} 2 ^ (b (q + t s))`, for `b s ≥ 1`. -/
theorem barAt_eq {b s : ℕ} (h : 1 ≤ b * s) (q k : ℕ) :
    barAt (2 ^ q) b s k = ∑ t ∈ range k, 2 ^ (b * (q + t * s)) := by
  have h2 : 2 ≤ 2 ^ (b * s) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (b * s) := Nat.pow_le_pow_right (by norm_num) h
  have hg := Nat.geomSum_eq h2 k
  have e1 : (2 ^ q) ^ b = 2 ^ (b * q) := by rw [← pow_mul, mul_comm]
  have e2 : 2 ^ (b * (s * k)) = (2 ^ (b * s)) ^ k := by rw [← pow_mul, mul_assoc]
  rw [barAt, e1, e2, ← hg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

/-- The bitmask of the cells `(i, j)`, `i < r`, `j < c`, of the `r × c` rectangle with rows of
length `w` (cell `(i, j)` has index `i * w + j`): `∑_{i < r} (2 ^ c - 1) 2 ^ (i w)`. -/
def rectMask (r c w : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i m => m + (2 ^ c - 1) * 2 ^ (i * w)) r

/-- `starts free s k` (for `k ≥ 1`) is `free &&& (free >>> s) &&& ⋯ &&& (free >>> ((k - 1) s))`:
its bit `q` is set iff the cells `q, q + s, …, q + (k - 1) s` all lie in `free`
(`testBit_starts`). -/
def starts (free s k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) free
    (fun t acc => Nat.land acc (Nat.shiftRight free ((t + 1) * s))) (k - 1)

/-- Bit `q` of `starts free s (k + 1)` is set iff bits `q, q + s, …, q + k s` of `free` are. -/
theorem testBit_starts (free s q k : ℕ) :
    (starts free s (k + 1)).testBit q = true ↔ ∀ t < k + 1, free.testBit (q + t * s) = true := by
  simp only [starts, Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    change (Nat.land (Nat.rec (motive := fun _ => ℕ) free
        (fun t acc => Nat.land acc (Nat.shiftRight free ((t + 1) * s))) k)
        (Nat.shiftRight free ((k + 1) * s))).testBit q = true ↔ _
    rw [Nat.land_eq, Nat.testBit_and, Bool.and_eq_true, ih, Nat.shiftRight_eq,
      Nat.testBit_shiftRight]
    constructor
    · rintro ⟨h1, h2⟩ t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
      · exact h1 t ht
      · subst ht; rwa [Nat.add_comm]
    · intro h
      exact ⟨fun t ht => h t (by omega), by rw [Nat.add_comm]; exact h (k + 1) (by omega)⟩

/-- `sumBits g fuel X` is the sum of `g (2 ^ q)` over the set bits `q` of `X`, if `X` has at most
`fuel` set bits: `X - (X &&& (X - 1))` is the lowest set bit `2 ^ q` of `X ≠ 0`, and
`X &&& (X - 1)` is `X` with that bit cleared. -/
def sumBits (g : ℕ → ℕ) (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih X =>
      bif Nat.beq X 0 then 0 else g (X - Nat.land X (X - 1)) + ih (Nat.land X (X - 1))) fuel

/-- `search w N L f k free lab` is the sum of `f lab'` over all ways of placing the tiles
`k, k - 1, …, 1` (in this order) at pairwise disjoint placements inside the set of free cells
`free` (rows of length `w`, all indices `< N`) that leave no cell free, where `lab'` is `lab`
plus the labels of the placed tiles (fields of `L` bits). Tile `k` goes horizontally at the first
cells `q` given by the set bits of `starts free 1 k`, or, if `k ≥ 2`, vertically at those of
`starts free w k`; its cells are then removed from `free`, and `k` is written into their fields
of `lab`. -/
def search (w N L : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun free lab => bif Nat.beq free 0 then f lab else 0)
    (fun k ih free lab =>
      sumBits (fun x => ih (free - barAt x 1 1 (k + 1)) (lab + (k + 1) * barAt x L 1 (k + 1)))
          N (starts free 1 (k + 1)) +
        bif Nat.ble 1 k then
          sumBits (fun x => ih (free - barAt x 1 w (k + 1)) (lab + (k + 1) * barAt x L w (k + 1)))
            N (starts free w (k + 1))
        else 0)

/-- The label of cell `p` in the labelling `lab` (fields of `L` bits): the field at bit position
`L * p`. -/
def field (L lab p : ℕ) : ℕ := Nat.land (Nat.shiftRight lab (L * p)) (2 ^ L - 1)

/-- The non-identity symmetries of the `r × c` rectangle, as maps on cell coordinates `(i, j)`:
the reflections in the horizontal and in the vertical axis, and the half-turn; if the rectangle is
a square (`r = c`), also the reflections in the two diagonals and the two quarter-turns. Together
with the identity they form the symmetry group of the rectangle. -/
def otherSymmetries (r c : ℕ) : List (ℕ × ℕ → ℕ × ℕ) :=
  [fun p => (r - 1 - p.1, p.2), fun p => (p.1, c - 1 - p.2),
    fun p => (r - 1 - p.1, c - 1 - p.2)] ++
  (if r = c then
    [fun p => (p.2, p.1), fun p => (c - 1 - p.2, r - 1 - p.1), fun p => (p.2, r - 1 - p.1),
      fun p => (c - 1 - p.2, p.1)]
  else [])

/-- Whether the symmetry `g` fixes the tiling with labelling `lab` (fields of `L` bits, rows of
length `w`) of the `r × c` rectangle: `label (g (i, j)) = label (i, j)` for all cells `(i, j)`.
(Tile `k` of `g • T` covers the `g`-image of tile `k` of `T`, so `g • T = T` iff the labelling is
`g`-invariant.) -/
def fixes (r c w L : ℕ) (g : ℕ × ℕ → ℕ × ℕ) (lab : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih =>
      Nat.rec (motive := fun _ => Bool) true
          (fun j ihj =>
            Nat.beq (field L lab ((g (i, j)).1 * w + (g (i, j)).2)) (field L lab (i * w + j)) &&
              ihj) c &&
        ih) r

/-- The size of the stabilizer of the tiling with labelling `lab`: the identity (which fixes every
tiling) plus the non-identity symmetries of the rectangle fixing it. -/
def stabCount (r c w L : ℕ) (lab : ℕ) : ℕ :=
  1 + List.rec (motive := fun _ => ℕ) 0
    (fun g _ ih => (bif fixes r c w L g lab then 1 else 0) + ih) (otherSymmetries r c)

/-- A394981: the number of tilings, up to the symmetries of the rectangle, of the
`rows n × cols n` rectangle (area `n (n + 1) / 2`, smallest perimeter) by the `n` tiles
`1 × 1, 1 × 2, …, 1 × n`, each used exactly once. By Burnside's lemma it is the sum of the
stabilizer sizes over all tilings (enumerated by `search`, starting from the whole rectangle free
and the empty labelling, with fields of `n` bits) divided by the order `1 + |otherSymmetries|` of
the symmetry group. -/
def a (n : ℕ) : ℕ :=
  let r := rows n
  let c := cols n
  let w := c + 1
  search w (r * w) n (stabCount r c w n) n (rectMask r c w) 0 /
    (1 + (otherSymmetries r c).length)

/-- The definition reproduces the first 9 terms listed in OEIS (offset 1, kernel-checked). -/
theorem a_data : (List.range 9).map (fun i => a (i + 1)) =
    [1, 1, 1, 4, 10, 40, 112, 448, 1360] := by
  decide +kernel

/-- The literal reading of the conjecture, which includes `n = 1`, fails there:
`a 2 = 1 ≠ 4 = 4 * a 1` (kernel-checked). This is why `statement` starts at `n = 3`. -/
theorem literal_fails_at_one : a (1 + 1) ≠ 4 * a 1 := by
  decide +kernel

/-- Conjecture (A394981, FORMULA section): if `n` is odd, then `a(n + 1) = 4 a(n)`; read for every
odd `n ≥ 3`, since the degenerate case `n = 1` fails (`literal_fails_at_one`). -/
def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → Odd n → a (n + 1) = 4 * a n

end Math0.Statements.A394981
