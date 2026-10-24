/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A367119: edges of the all-chords graph of a triangle with `n` general points per side

Source: https://oeis.org/A367119, _Scott R. Shannon_ and _N. J. A. Sloane_, Nov 05 2023
(FORMULA section). Verbatim:
> Conjecture: a(n) = (3/2)*(3*n^4 + 4*n^3 + 3*n^2 + 4*n + 2).

The entry's definition (offset `0`): "Place n points in general position on each side of an
equilateral triangle, and join every pair of the 3*n+3 boundary points by a chord; sequence gives
number of edges in the resulting planar graph." Comment: "'In general position' implies that the
internal lines (or chords) only have simple intersections. There is no interior point where three
or more chords meet." Data: `3, 24, 153, 588, 1635, 3708, 7329, 13128, 21843, 34320, 51513, …`.

## Encoding

*Geometry (used by `statement`).* The plane is `ℂ`. The equilateral triangle `triangle` is the
convex hull of `corner 0 = 0`, `corner 1 = 1`, `corner 2 = 1/2 + (√3/2) i`; side `j` (`j : Fin 3`,
so `2 + 1 = 0`) is the segment from `corner j` to `corner (j + 1)`.
* `IsPlacement n B`: the finite set `B ⊆ ℂ` of boundary points consists of the three corners
  together with exactly `n` points in the relative interior (`openSegment`) of each side, and
  nothing else (every point of `B` lies on a closed side). So `B` has `3n+3` points.
* The drawn segments `drawn B` are the segments `[p, q]` for all pairs `p ≠ q` of points of `B`
  ("join every pair of the 3n+3 boundary points by a chord"). A pair of points on a common side
  gives a piece of that side, so the sides of the triangle belong to the drawing.
* `GeneralPosition B` is the entry's comment: no point of the interior of the triangle lies on
  three pairwise distinct drawn segments. No other condition is imposed ("general position" is
  read exactly as the comment explains it).
* The planar graph. Its vertices (`vertices B`) are the points of `B` and the points where two
  drawn segments meet in a single point (`s ∩ t = {z}`; this excludes overlapping pieces of a
  common side, whose points are not vertices). Two distinct vertices `u, v` are adjacent
  (`planarGraph B`, a `SimpleGraph ℂ` whose non-vertices are isolated) iff they lie on a common
  drawn segment and no vertex lies strictly between them (`openSegment ℝ u v`), i.e. `[u, v]`
  is a piece of the drawing between consecutive vertices. `edges B` is the number of edges of
  this graph (`edgeSet.ncard`; the edge set is finite since the vertex set is).
* The entry's `a(n)` is `edges B` for any `B` with `IsPlacement n B` and `GeneralPosition B`
  (the entry presupposes that this number does not depend on the choice of `B`). The conjecture
  is therefore read as: for every `n ≥ 0` (offset `0`) and every placement `B` of `n` points per
  side in general position, `edges B = (3/2)(3n^4 + 4n^3 + 3n^2 + 4n + 2)`, as rationals.

*The computable sequence `a`.* For the data check the count is computed combinatorially; the
link `a n = edges B` (for `B` as above) is the intended meaning and is not proved here.
Number the `3n+3` boundary points `0, 1, …, 3n+2` in cyclic order, with `corner j` at position
`j(n+1)`; the closed side `j` consists of the positions `j(n+1), …, (j+1)(n+1)` (position
`3(n+1)` being `0`). A pair of positions on a common closed side spans a piece of a side, and the
boundary is cut by the `3n+3` points into `3n+3` edges. Every other pair `x < y`
(`chordList n`) spans a chord whose relative interior lies in the open triangle (a segment
joining two boundary points of a convex polygon that are not on a common side). Two such chords
meet in the open triangle iff their endpoints are four distinct positions that interleave in the
cyclic order (`crosses`); chords sharing an endpoint meet only there, and two distinct chords
never overlap (a line not containing a side meets the boundary in at most two points). In general
position the points where a given chord meets the other chords are pairwise distinct, so the
chord is cut into `1 +` (number of chords crossing it) edges. Hence
`a n = (3n+3) + ∑_{chords c} (1 + #{chords crossing c})`.

A Python transcription of `a` reproduces the listed terms for `n = 0, …, 15`. `a_data` checks
the first 11 listed terms `a 0, …, a 10` in the kernel.
-/

namespace Math0.Statements.A367119

/-! ### The geometric definition -/

/-- The corners `0`, `1`, `1/2 + (√3/2) i` of an equilateral triangle in the plane `ℂ`. -/
noncomputable def corner : Fin 3 → ℂ := ![0, 1, ⟨1 / 2, Real.sqrt 3 / 2⟩]

/-- The closed equilateral triangle. -/
noncomputable def triangle : Set ℂ := convexHull ℝ (Set.range corner)

/-- `B` is a placement of `n` points on each side of the triangle: `B` contains the three
corners, exactly `n` points in the relative interior of each side, and no other points (every
point of `B` lies on a closed side). -/
def IsPlacement (n : ℕ) (B : Finset ℂ) : Prop :=
  (∀ j : Fin 3, corner j ∈ B) ∧
  (∀ z ∈ B, ∃ j : Fin 3, z ∈ segment ℝ (corner j) (corner (j + 1))) ∧
  (∀ j : Fin 3, ((B : Set ℂ) ∩ openSegment ℝ (corner j) (corner (j + 1))).ncard = n)

/-- The drawn segments: the segments joining every pair of distinct boundary points. -/
def drawn (B : Finset ℂ) : Set (Set ℂ) :=
  {s | ∃ p ∈ B, ∃ q ∈ B, p ≠ q ∧ s = segment ℝ p q}

/-- General position (the entry's comment): there is no interior point of the triangle where
three or more of the drawn chords meet. -/
def GeneralPosition (B : Finset ℂ) : Prop :=
  ∀ z ∈ interior triangle, ∀ s₁ ∈ drawn B, ∀ s₂ ∈ drawn B, ∀ s₃ ∈ drawn B,
    z ∈ s₁ → z ∈ s₂ → z ∈ s₃ → s₁ = s₂ ∨ s₁ = s₃ ∨ s₂ = s₃

/-- The vertices of the planar graph: the boundary points, and the points where two drawn
segments meet in a single point. -/
def vertices (B : Finset ℂ) : Set ℂ :=
  (B : Set ℂ) ∪ {z | ∃ s ∈ drawn B, ∃ t ∈ drawn B, s ∩ t = {z}}

/-- The planar graph (on the vertex type `ℂ`, points that are not vertices being isolated): two
distinct vertices are adjacent iff they lie on a common drawn segment and no vertex lies strictly
between them. -/
def planarGraph (B : Finset ℂ) : SimpleGraph ℂ :=
  SimpleGraph.fromRel fun u v =>
    u ∈ vertices B ∧ v ∈ vertices B ∧ (∃ s ∈ drawn B, u ∈ s ∧ v ∈ s) ∧
      ∀ w ∈ vertices B, w ∉ openSegment ℝ u v

/-- The number of edges of the planar graph obtained from the boundary points `B`. -/
noncomputable def edges (B : Finset ℂ) : ℕ := (planarGraph B).edgeSet.ncard

/-! ### The combinatorial computation -/

/-- Boundary position `x` (`0 ≤ x < 3n+3`, corner `j` at position `j(n+1)`) lies on the closed
side `j` (`j < 3`), which consists of the positions `j(n+1), …, (j+1)(n+1)`, position
`3(n+1)` being position `0`. -/
def onSide (n j x : ℕ) : Bool :=
  (j * (n + 1) ≤ x && x ≤ (j + 1) * (n + 1)) || (j == 2 && x == 0)

/-- The positions `x < y` are not on a common closed side, so they span a chord through the
interior of the triangle. -/
def isChord (n x y : ℕ) : Bool :=
  x < y && !((onSide n 0 x && onSide n 0 y) || (onSide n 1 x && onSide n 1 y) ||
    (onSide n 2 x && onSide n 2 y))

/-- The interior chords, as pairs of positions `(x, y)` with `x < y`. -/
def chordList (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (3 * n + 3)).flatMap fun x =>
    ((List.range (3 * n + 3)).filter fun y => isChord n x y).map fun y => (x, y)

/-- Two chords `(x, y)`, `(u, v)` (`x < y`, `u < v`) cross inside the triangle: their four
endpoints are distinct and interleave in the cyclic order. -/
def crosses (c d : ℕ × ℕ) : Bool :=
  (c.1 < d.1 && d.1 < c.2 && c.2 < d.2) || (d.1 < c.1 && c.1 < d.2 && d.2 < c.2)

/-- The number of edges lying on the chords: each chord is cut into `1 +` (number of chords
crossing it) edges. -/
def chordEdges (cs : List (ℕ × ℕ)) : ℕ :=
  (cs.map fun c => 1 + cs.countP fun d => crosses c d).sum

/-- A367119: the number of edges of the planar graph formed by all chords joining the `3n+3`
boundary points of an equilateral triangle with `n` points in general position on each side:
`3n+3` boundary edges plus the edges on the interior chords. -/
def a (n : ℕ) : ℕ :=
  (3 * n + 3) + chordEdges (chordList n)

/-- The definition reproduces the first terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 11).map (fun i => a i) =
    [3, 24, 153, 588, 1635, 3708, 7329, 13128, 21843, 34320, 51513] := by
  decide +kernel

/-- Conjecture (Shannon and Sloane, 2023): for every `n ≥ 0`, if `n` points are placed in
general position on each side of an equilateral triangle and every pair of the `3n+3` boundary
points is joined by a chord, the resulting planar graph has
`(3/2)(3n^4 + 4n^3 + 3n^2 + 4n + 2)` edges. -/
def statement : Prop :=
  ∀ (n : ℕ) (B : Finset ℂ), IsPlacement n B → GeneralPosition B →
    (edges B : ℚ) = 3 / 2 * (3 * n ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 4 * n + 2)

end Math0.Statements.A367119
