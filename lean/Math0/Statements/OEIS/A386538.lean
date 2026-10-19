/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A386538: maximum area of a lattice polygon inside a circle of radius `n`

Source: https://oeis.org/A386538, _Felix Huber_, Aug 05 2025. Verbatim (COMMENTS section):
> Conjecture: The maximum possible area of a polygon within the circle would be the same if only
> the vertices but not the center were fixed on grid points.

The entry's definition (offset 0): "a(n) is the maximum possible area of a polygon within a
circle of radius n, where both the center and the vertices lie on points of a unit square grid."

## Encoding

* The unit square grid is `ℤ × ℤ ⊆ ℝ × ℝ`; "within a circle of radius `r` with center `c`" means
  in the closed disk `(x - c₁)² + (y - c₂)² ≤ r²` (boundary allowed; `a(1) = 2`, the square with
  vertices `(±1, 0), (0, ±1)`, requires this). `latticeDisk c r` is the set of grid points in
  that disk.
* Polygon areas. For a finite point set `S`, the largest area of a polygon whose vertices lie in
  `S` is the area of the convex hull of `S`: the region of any polygon with vertices in `S` lies
  in `convexHull S`, and `convexHull S` is itself a convex polygon with vertices in `S` (it lies
  in the disk because the disk is convex). Degenerate cases (fewer than three non-collinear points)
  give area `0`. So the maximum area of a polygon with grid vertices within the circle of radius
  `r` around `c` is `maxArea c r = volume (convexHull ℝ (latticeDisk c r))`, the Lebesgue measure
  in `ℝ × ℝ`.
* By translation invariance, the center on a grid point may be taken to be the origin; the
  entry's `a(n)` is `maxArea 0 n` (a real number, in fact an even integer).
* The computable `a n` is the same quantity computed exactly: the grid points in the disk of
  radius `n` around the origin are listed in lexicographic order (`pts`), their convex hull is
  computed by Andrew's monotone chain algorithm (`chain` builds the lower hull from the sorted
  list and the upper hull from the reversed list), and twice the area is the shoelace sum over
  both chains (`twiceArea`). Since the hull is invariant under the rotation by 90°, twice the area
  is a multiple of 4, so `a n = twiceArea n / 2` is exact. (`a n = (maxArea 0 n).toReal` is the
  intended meaning; it is not proved here.) A Python transcription and `scipy.spatial.ConvexHull`
  give the same values for `n ≤ 48`.
* Data. `a_data` checks the listed terms `a(0), …, a(12)`. The listed terms from `a(13)` on are
  not all the true maximum areas: e.g. the entry lists `a(13) = 512`, but the convex 20-gon with
  vertices `(±13, 0), (±12, ±5), (±10, ±8), (±8, ±10), (±5, ±12), (0, ±13)` (all on the circle)
  has area 516, and `a_13` checks `a 13 = 516`. In the range `13 ≤ n ≤ 48` of the listed data,
  the definition (and `a`) agrees with the listed values exactly for
  `n = 14, 15, 16, 19, 20, 21, 24, 25`, which `a_data_more` checks; it gives larger values for all
  other `n` in that range. The conjecture is read with its own definition of `a(n)` (the maximum
  area), not with the listed numbers.
* Reading of the conjecture: for every `n ≥ 0` (the entry's offset), the maximum area of a
  polygon with grid vertices within a circle of radius `n` whose center is an arbitrary point
  `c ∈ ℝ²` (the maximum taken over the center as well) equals the maximum with a grid-point
  center, i.e. `⨆ c, maxArea c n = maxArea 0 n`. Since `c = 0` is allowed, this is equivalent to
  `maxArea c n ≤ maxArea 0 n` for all `c`.
-/

namespace Math0.Statements.A386538

open MeasureTheory

/-! ### The computable sequence -/

/-- The grid points `(x, y) ∈ ℤ²` with `x² + y² ≤ n²`, in lexicographic order (by `x`, then `y`). -/
def pts (n : ℕ) : List (ℤ × ℤ) :=
  (List.range (2 * n + 1)).flatMap fun i => (List.range (2 * n + 1)).filterMap fun j =>
    let x : ℤ := (i : ℤ) - n
    let y : ℤ := (j : ℤ) - n
    if x * x + y * y ≤ (n : ℤ) * n then some (x, y) else none

/-- The cross product `(a - o) × (b - o)`; it is positive iff `o, a, b` make a left turn. -/
def cross (o a b : ℤ × ℤ) : ℤ := (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)

/-- One step of the monotone chain algorithm: the stack `s` holds the current chain with its last
point first; pop the last point while it does not make a strict left turn with `p`, then push
`p`. -/
def push (p : ℤ × ℤ) : List (ℤ × ℤ) → List (ℤ × ℤ)
  | a :: b :: rest => if cross b a p ≤ 0 then push p (b :: rest) else p :: a :: b :: rest
  | s => p :: s
termination_by structural s => s

/-- The monotone chain of a list of points (the lower hull for a lexicographically sorted list,
the upper hull for the reversed list), as a stack with its last point first. -/
def chain (l : List (ℤ × ℤ)) : List (ℤ × ℤ) := l.foldl (fun s p => push p s) []

/-- The shoelace sum `Σ (xᵢ yᵢ₊₁ - xᵢ₊₁ yᵢ)` over the consecutive points of an open path. -/
def pathCross : List (ℤ × ℤ) → ℤ
  | a :: b :: rest => (a.1 * b.2 - b.1 * a.2) + pathCross (b :: rest)
  | _ => 0
termination_by structural s => s

/-- Twice the area of the convex hull of the grid points in the closed disk of radius `n` around
the origin: the lower chain (first to last point) followed by the upper chain (last to first
point) is the hull boundary traversed counterclockwise; the stacks hold the chains reversed,
hence the sign. -/
def twiceArea (n : ℕ) : ℤ :=
  -(pathCross (chain (pts n)) + pathCross (chain (pts n).reverse))

/-- `a n` is the maximum area of a polygon with vertices on grid points within the circle of
radius `n` centered at a grid point, computed as the area of the convex hull of the grid points
in the closed disk of radius `n` around the origin. -/
def a (n : ℕ) : ℕ := (twiceArea n).toNat / 2

/-- The definition reproduces the first terms listed in OEIS, `a(0), …, a(12)` (kernel-checked). -/
theorem a_data : (List.range 13).map (fun i => a (i + 0)) =
    [0, 2, 8, 24, 42, 74, 104, 138, 186, 240, 304, 362, 424] := by
  decide +kernel

/-- The listed terms `a(13)` to `a(48)` that agree with the definition (kernel-checked). -/
theorem a_data_more : [14, 15, 16, 19, 20, 21, 24, 25].map a =
    [594, 690, 776, 1104, 1232, 1346, 1762, 1930] := by
  decide +kernel

/-- The true value at `n = 13` (the entry lists `512`): the convex hull of the grid points in the
disk of radius 13 is the 20-gon with vertices `(±13, 0), (±12, ±5), (±10, ±8), (±8, ±10),
(±5, ±12), (0, ±13)`, of area 516. -/
theorem a_13 : a 13 = 516 := by
  decide +kernel

/-! ### The geometric quantity and the conjecture -/

/-- The grid points `(x, y) ∈ ℤ²` (as points of `ℝ × ℝ`) in the closed disk of radius `r` around
`c`. -/
def latticeDisk (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ x y : ℤ, p = ((x : ℝ), (y : ℝ)) ∧ ((x : ℝ) - c.1) ^ 2 + ((y : ℝ) - c.2) ^ 2 ≤ r ^ 2}

/-- The maximum area of a polygon with vertices on grid points within the circle of radius `r`
around `c`: the Lebesgue measure of the convex hull of `latticeDisk c r`. -/
noncomputable def maxArea (c : ℝ × ℝ) (r : ℝ) : ENNReal :=
  volume (convexHull ℝ (latticeDisk c r))

/-- The conjecture: for every `n ≥ 0`, the maximum area of a polygon with grid vertices within a
circle of radius `n` whose center is an arbitrary point of the plane (maximum over the center as
well) equals the maximum area when the center is a grid point (the origin), i.e. `a(n)`. -/
def statement : Prop :=
  ∀ n : ℕ, (⨆ c : ℝ × ℝ, maxArea c n) = maxArea 0 n

end Math0.Statements.A386538
