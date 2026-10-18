/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A397315: maximum blackout of an `n × k` grid keeping all lattice rectangles identifiable

Source: https://oeis.org/A397315, _Arjun Pemmasani_, Sep 02 2026. Verbatim (COMMENTS section):
> Conjecture: T(n,m) = n+m whenever min(n,m) >= 4, except T(4,4) = 7 and T(4,5) = 8 (verified
> on seven cells through 6 X 6).

The entry's definition: "Table read by antidiagonals: T(n,k) = maximum number of points that can
be blacked out of an n X k grid of points so that every rectangle with all four vertices on grid
points (tilted rectangles included) is uniquely identifiable from its set of visible vertices;
n, k >= 2." The comments make "identifiable" precise: the map `R ↦ C(R) \ S` (vertex set of the
rectangle minus the blacked-out set `S`) must be injective over all rectangles.

## Encoding

* The `n × k` grid is `{0, …, k-1} × {0, …, n-1} ⊆ ℤ × ℤ`, exactly as in the entry's Python and
  PARI programs (`x < k`, `y < n`). Its points are numbered `i = x * n + y`, `0 ≤ i < n * k`, so
  point `i` is `pt n i = (i / n, i % n)`; a set of grid points is a bitmask (bit `i` set iff
  point `i` is in the set).
* A rectangle (tilted ones included, squares included) is the vertex set `{a, b, c, d}` of three
  pairwise distinct grid points `a, b, c` with a right angle at `b`, i.e.
  `(a - b) · (c - b) = 0`, whose fourth vertex `d = a + c - b` is again a grid point. These are
  exactly the conditions of the entry's programs. `rects n k` lists every such vertex set once
  (duplicates, which arise from the 8 ways to choose `(a, b, c)` for one rectangle, are erased).
* A blackout `B ⊆ grid` is valid iff the visible parts `R \ B` of the distinct rectangles `R` are
  pairwise distinct, i.e. `R ↦ R \ B` is injective on rectangles. `T n k` is the largest number of
  points of a valid blackout, the maximum being taken over all `2 ^ (n * k)` subsets of the grid
  (the empty blackout is always valid). For speed in the kernel, the list recursions in
  `notMem` and `pairwiseDistinct` are written with `List.rec`, the bit operations with
  `Nat.land`/`Nat.xor`/`Nat.beq`, and `card` counts bits by halving; they compute exactly what
  their docstrings say.
* `a` is the table flattened by antidiagonals as in the entry (`n + k = 4, 5, 6, …`, and within an
  antidiagonal `n = 2, 3, …`, `k = (n + k) - n`, which is the order of the entry's Python program),
  indexed from the entry's offset `2`: `a 2 = T 2 2`, `a 3 = T 2 3`, `a 4 = T 3 2`, ….
  (`a 0 = a 1 = 0` are junk values.) The table is symmetric, `T n k = T k n`, by transposition.
* Reading of the conjecture: for all `n, m` with `min(n, m) ≥ 4`, `T(n, m) = n + m`, except
  `T(4,4) = 7` and `T(4,5) = 8`. Since the table is symmetric (and the entry's data list
  `T(5,4) = 8`), the exception `T(4,5) = 8` is read as covering both cells `(4,5)` and `(5,4)`;
  reading it as covering `(4,5)` alone would make the conjecture contradict the entry's own data
  at `(5,4)`. The two exceptional values are part of the statement.
* Kernel check: the first 10 terms (antidiagonals `n + k ≤ 7`, grids of at most 12 points) are
  checked, each value `T n k` by its own `decide +kernel` (one joint `decide` over all ten runs
  out of memory), and `a_data` assembles them. These ten checks take about a minute; the two
  12-point grids `3 × 4` and `4 × 3` (4096 subsets each) dominate. The next term needs another
  12-point grid and the terms after it grids of 15 or more points (`2 ^ 15` or more subsets),
  which is beyond the kernel in that budget. (A Python transcription of the same encoding
  reproduces the first 15 listed terms.)
-/

namespace Math0.Statements.A397315

/-- The coordinates `(x, y) = (i / n, i % n)` of the point with index `i` of the `n × k` grid
`{0, …, k-1} × {0, …, n-1}`; the indices `0, …, n * k - 1` enumerate the grid. -/
def pt (n i : ℕ) : ℤ × ℤ := (((i / n : ℕ) : ℤ), ((i % n : ℕ) : ℤ))

/-- Whether an integer point lies in the grid `{0, …, k-1} × {0, …, n-1}`. -/
def inGrid (n k : ℕ) (p : ℤ × ℤ) : Bool :=
  decide (0 ≤ p.1) && decide (p.1 < k) && decide (0 ≤ p.2) && decide (p.2 < n)

/-- The index `x * n + y` of a grid point `(x, y)` (the inverse of `pt n` on the grid). -/
def idx (n : ℕ) (p : ℤ × ℤ) : ℕ := p.1.toNat * n + p.2.toNat

/-- For grid point indices `a, b, c`: if `a, b, c` are pairwise distinct, the angle at `b` is right
(`(a - b) · (c - b) = 0`) and the fourth vertex `d = a + c - b` lies in the grid, the vertex set
`{a, b, c, d}` of this rectangle as a bitmask; otherwise `none`. -/
def rectMask? (n k a b c : ℕ) : Option ℕ :=
  let A := pt n a
  let B := pt n b
  let C := pt n c
  let D := A + C - B
  if a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ (A.1 - B.1) * (C.1 - B.1) + (A.2 - B.2) * (C.2 - B.2) = 0 ∧
      inGrid n k D = true then
    some (2 ^ a ||| 2 ^ b ||| 2 ^ c ||| 2 ^ idx n D)
  else none

/-- The vertex sets (as bitmasks) of all rectangles, tilted ones included, with all four vertices
in the `n × k` grid, each listed once. -/
def rects (n k : ℕ) : List ℕ :=
  ((List.range (n * k)).flatMap fun a => (List.range (n * k)).flatMap fun b =>
    (List.range (n * k)).filterMap fun c => rectMask? n k a b c).eraseDups

/-- The visible part `R \ B` of a vertex set `R` when the points of `B` are blacked out
(bitmasks: clear in `R` the bits of `B`). -/
def visible (R B : ℕ) : ℕ := Nat.xor R (Nat.land R B)

/-- `true` iff `x` does not occur in `l`. -/
def notMem (x : ℕ) (l : List ℕ) : Bool := l.rec true fun y _ ih => !(Nat.beq x y) && ih

/-- `true` iff the entries of `l` are pairwise distinct (i.e. `l.Nodup`). -/
def pairwiseDistinct (l : List ℕ) : Bool := l.rec true fun x xs ih => notMem x xs && ih

/-- `B` (a set of grid points, as a bitmask) is a valid blackout of the `n × k` grid: distinct
rectangles have distinct visible parts, i.e. `R ↦ R \ B` is injective on the rectangles. -/
def isValidBlackout (n k B : ℕ) : Bool := pairwiseDistinct ((rects n k).map (visible · B))

/-- `card len B` is the number of points with index `< len` in the set `B` (a bitmask), i.e. the
number of 1 bits among the lowest `len` binary digits of `B`. -/
def card : ℕ → ℕ → ℕ
  | 0, _ => 0
  | len + 1, B => B % 2 + card len (B / 2)

/-- A397315 as a table: `T n k` is the maximum number of points that can be blacked out of the
`n × k` grid so that every rectangle with all four vertices on grid points (tilted rectangles
included) is uniquely identifiable from its set of visible vertices. The maximum runs over all
subsets `B` of the grid, i.e. all bitmasks `B < 2 ^ (n * k)`. -/
def T (n k : ℕ) : ℕ :=
  ((List.range (2 ^ (n * k))).filter (isValidBlackout n k)).foldr
    (fun B m => max (card (n * k) B) m) 0

/-- The `j`-th cell `(n, k)` (`j ≥ 0`) of the table in the entry's reading order: by antidiagonals
`n + k = 4, 5, 6, …`, and within an antidiagonal by increasing `n`. (The list below has
`(j + 1)(j + 2)/2 > j` entries, so the default value is never used.) -/
def cell (j : ℕ) : ℕ × ℕ :=
  ((List.range (j + 1)).flatMap fun d =>
    (List.range (d + 1)).map fun i => (2 + i, 2 + d - i)).getD j (0, 0)

/-- A397315 as a sequence, with the entry's offset `2`: `a i = T n k` for the `(i - 2)`-th cell
`(n, k)` in the antidiagonal reading order (`a 0 = a 1 = 0` are junk values). -/
def a (i : ℕ) : ℕ := if i < 2 then 0 else T (cell (i - 2)).1 (cell (i - 2)).2

/-- The reading order of the cells: `(2,2), (2,3), (3,2), (2,4), (3,3), (4,2), …`. -/
theorem cell_data : (List.range 15).map cell =
    [(2, 2), (2, 3), (3, 2), (2, 4), (3, 3), (4, 2), (2, 5), (3, 4), (4, 3), (5, 2),
      (2, 6), (3, 5), (4, 4), (5, 3), (6, 2)] := by
  decide +kernel

/-- `a (j + 2)` is the value of `T` at the `j`-th cell. -/
theorem a_add_two (j : ℕ) : a (j + 2) = T (cell j).1 (cell j).2 := by
  simp [a]

/-! The values of `T` on the first 10 cells, each checked by the kernel separately. -/

theorem T_2_2 : T 2 2 = 4 := by decide +kernel
theorem T_2_3 : T 2 3 = 4 := by decide +kernel
theorem T_3_2 : T 3 2 = 4 := by decide +kernel
theorem T_2_4 : T 2 4 = 5 := by decide +kernel
theorem T_3_3 : T 3 3 = 5 := by decide +kernel
theorem T_4_2 : T 4 2 = 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem T_2_5 : T 2 5 = 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem T_3_4 : T 3 4 = 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem T_4_3 : T 4 3 = 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem T_5_2 : T 5 2 = 6 := by decide +kernel

/-- The definition reproduces the first 10 terms listed in OEIS (each value of `T` kernel-checked
by `decide +kernel` above; the cells by `cell_data`). -/
theorem a_data : (List.range 10).map (fun i => a (i + 2)) = [4, 4, 4, 5, 5, 5, 6, 6, 6, 6] := by
  have hcell : (List.range 10).map cell =
      [(2, 2), (2, 3), (3, 2), (2, 4), (3, 3), (4, 2), (2, 5), (3, 4), (4, 3), (5, 2)] := by
    decide +kernel
  rw [List.map_congr_left (fun j _ => a_add_two j),
    show (fun j => T (cell j).1 (cell j).2) = (fun c : ℕ × ℕ => T c.1 c.2) ∘ cell from rfl,
    ← List.map_map, hcell]
  simp only [List.map_cons, List.map_nil, T_2_2, T_2_3, T_3_2, T_2_4, T_3_3, T_4_2, T_2_5,
    T_3_4, T_4_3, T_5_2]

/-- Conjecture (Pemmasani, A397315): `T(n, m) = n + m` whenever `min(n, m) ≥ 4`, except
`T(4,4) = 7` and `T(4,5) = 8` (with `T(5,4) = T(4,5) = 8` by symmetry). -/
def statement : Prop :=
  ∀ n m : ℕ, 4 ≤ min n m →
    T n m = if n = 4 ∧ m = 4 then 7
      else if (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 4) then 8
      else n + m

end Math0.Statements.A397315
