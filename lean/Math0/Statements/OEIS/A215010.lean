/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A215010: equiangular convex polygons with sides in arithmetic progression

Source: https://oeis.org/A215010, Robin Garcia, Jul 31 2012. Verbatim:
> Conjecture: hexagons are the only simple convex polygons with equal interior angles with
> such property, due to the fact that cos(Pi/3) = 1/2.

The "property" is the one in the entry's name: "Integer side lengths in arithmetic progression
of simple convex hexagons with equal interior angles. Sequence gives the values of m for sides
of lengths t+m*d, counterclockwise, for the two primitive solutions." So the `N` sides of the
polygon are the `N` terms `t, t+d, …, t+(N-1)d` of an arithmetic progression of positive
integers, in some order.

## Encoding

*Polygons.* A simple convex polygon with equal interior angles, traversed counterclockwise,
turns by the same exterior angle `2π/N` at each vertex. After a rotation its `k`-th edge vector
is `s k • ζ ^ k` with `ζ = exp (2πi/N)`, so it closes up iff `∑ k, s k • ζ ^ k = 0`.
Conversely, for positive lengths `s` with `∑ k, s k • ζ ^ k = 0` the closed path with vertices
`P j = ∑ k < j, s k • ζ ^ k` turns left by `2π/N` at every vertex (total turning `2π`). It is
therefore a simple convex polygon with every interior angle equal to `(N-2)π/N`. So an
equiangular simple convex `N`-gon with consecutive sides `s 0, …, s (N-1)` exists iff
`3 ≤ N`, every `s k > 0` and `∑ k, s k • ζ ^ k = 0`. This is `IsEquiangularPolygon`.

*Arithmetic progressions.* Integer side lengths forming an arithmetic progression are
`t + m d` for `m = 0, …, N-1`, in the order given by a permutation `σ` of `Fin N`. We take
`t, d : ℕ` with `d ≥ 1`. A negative difference is the same set read backwards. `d = 0` is
excluded: the sides would all be equal, regular polygons exist for every `N`, and the
conjecture would be trivially false; the entry's solutions all use distinct values of `m`.
Positivity of the sides (so `t ≥ 1`) is part of `IsEquiangularPolygon`.

*Reading of "only".* `statement` is the uniqueness claim: every such polygon is a hexagon.
That hexagons do have the property is the content of the sequence itself (data below).

*The sequence.* The data `0,5,1,3,2,4,0,5,2,1,4,3` (offset 1) are the two primitive
solutions `m = (0,5,1,3,2,4)` and `(0,5,2,1,4,3)` concatenated. For `N = 6` we have
`∑ k, (t + m k d) ζ ^ k = d ∑ k, m k ζ ^ k` because `∑ k, ζ ^ k = 0`, so whether the hexagon
closes depends only on the pattern `m`. With `ζ = exp (iπ/3)`, `2 Re ζ ^ k = 2,1,-1,-2,-1,1` and
`(2/√3) Im ζ ^ k = 0,1,1,0,-1,-1` for `k = 0, …, 5`. So `∑ m k ζ ^ k = 0` iff the two integer
dot products `hexCos ⬝ m` and `hexSin ⬝ m` vanish (`hexCloses`). `hexCloses_iff` proves this
equivalence with the closing condition of `IsEquiangularPolygon` for `N = 6`, and an example
checks the entry's hexagon `(1,6,2,4,3,5)` against `IsEquiangularPolygon`. Patterns related by the
dihedral symmetries of the hexagon (rotation and reading direction) give the same hexagon up to
congruence. The entry's normal form starts at the shortest side (`m 0 = 0`) and continues
toward the longer of its two neighbours (`m 1 > m 5`). For example, the comment's hexagon
`(2,6,4,5,3,7)` is written as `(2,7,3,5,4,6)`, i.e. `m = (0,5,1,3,2,4)`. The two normal forms
are listed in lexicographic order. `a n` for `n` outside `1..12` is `0` (the sequence is
finite, keyword `fini`).
-/

namespace Math0.Statements.A215010

/-- All orderings of the list `l`, generated in lexicographic order when `l` is sorted
(`fuel` should be `l.length`; it only makes the recursion structural). -/
def lexPerms : ℕ → List ℕ → List (List ℕ)
  | 0, _ => [[]]
  | fuel + 1, l => l.flatMap fun x => (lexPerms fuel (l.erase x)).map (x :: ·)

/-- `2 cos (k π / 3)` for `k = 0, …, 5`: twice the real part of `exp (iπ/3) ^ k`. -/
def hexCos : List ℤ := [2, 1, -1, -2, -1, 1]

/-- `(2/√3) sin (k π / 3)` for `k = 0, …, 5`: the imaginary part of `exp (iπ/3) ^ k`,
times `2/√3`. -/
def hexSin : List ℤ := [0, 1, 1, 0, -1, -1]

/-- Integer dot product of a coefficient list with a list of naturals. -/
def dot (c : List ℤ) (m : List ℕ) : ℤ := (List.zipWith (fun x y => x * (y : ℤ)) c m).sum

/-- The equiangular hexagon with consecutive sides `t + m k * d` (`d > 0`) closes up, i.e.
`∑ k, m k * exp (iπ/3) ^ k = 0` (real and imaginary parts, rescaled to integers). -/
def hexCloses (m : List ℕ) : Bool := dot hexCos m == 0 && dot hexSin m == 0

/-- The entry's normal form under the dihedral symmetries of the hexagon: start at the shortest
side (`m 0 = 0`) and go toward the longer neighbour (`m 1 > m 5`). -/
def normalForm (m : List ℕ) : Bool := m.getD 0 0 == 0 && m.getD 5 0 < m.getD 1 0

/-- The primitive solutions: orderings `m` of `0, …, 5` such that the equiangular hexagon with
sides `t + m k * d`, counterclockwise, closes up, in normal form, in lexicographic order. -/
def primitiveSolutions : List (List ℕ) :=
  (lexPerms 6 (List.range 6)).filter fun m => hexCloses m && normalForm m

/-- A215010 (offset 1): the values of `m` for sides of lengths `t + m*d`, counterclockwise, of
the two primitive solutions (integer side lengths in arithmetic progression of simple convex
hexagons with equal interior angles), concatenated. `0` outside the 12 listed terms. -/
def a (n : ℕ) : ℕ := primitiveSolutions.flatten.getD (n - 1) 0

/-- The definition reproduces all 12 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 12).map (fun i => a (i + 1)) = [0, 5, 1, 3, 2, 4, 0, 5, 2, 1, 4, 3] := by
  decide +kernel

/-- There are exactly two primitive solutions, so the sequence has exactly 12 terms. -/
theorem primitiveSolutions_length : primitiveSolutions.length = 2 := by
  decide +kernel

/-- Direction of the `k`-th edge of an equiangular `N`-gon traversed counterclockwise:
`exp (2πi k / N)` (every exterior angle is `2π/N`). -/
noncomputable def edgeDir (N k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / N)

/-- A simple convex `N`-gon with equal interior angles whose consecutive sides, counterclockwise,
have lengths `s 0, …, s (N-1)` exists: `N ≥ 3`, all sides are positive, and the edge vectors
`s k • exp (2πi k / N)` sum to zero (see the module docstring for the equivalence). -/
def IsEquiangularPolygon (N : ℕ) (s : Fin N → ℕ) : Prop :=
  3 ≤ N ∧ (∀ k, 0 < s k) ∧ ∑ k : Fin N, (s k : ℂ) * edgeDir N k = 0

/-! ### Sanity checks linking `IsEquiangularPolygon` to `hexCloses` -/

/-- `exp (2πi/6) = 1/2 + (√3/2) i`. -/
theorem edgeDir_six_one : edgeDir 6 1 = 1 / 2 + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  unfold edgeDir
  have : (2 * Real.pi * Complex.I * ((1 : ℕ) : ℂ) / ((6 : ℕ) : ℂ)) =
      ((Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast; ring

theorem edgeDir_six (k : ℕ) : edgeDir 6 k = edgeDir 6 1 ^ k := by
  unfold edgeDir
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- For hexagons, the closing condition of `IsEquiangularPolygon` is exactly `hexCloses`. -/
theorem hexCloses_iff (m : Fin 6 → ℕ) :
    ∑ k : Fin 6, (m k : ℂ) * edgeDir 6 k = 0 ↔ hexCloses (List.ofFn m) = true := by
  set ζ := edgeDir 6 1 with hζ
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : ζ ^ 2 = ζ - 1 := by
    rw [hζ, edgeDir_six_one]
    apply Complex.ext <;> simp [pow_two] <;> nlinarith [hs]
  have hsum : ∑ k : Fin 6, (m k : ℂ) * edgeDir 6 k =
      (((m 0 : ℤ) - m 2 - m 3 + m 5 : ℤ) : ℂ) + (((m 1 : ℤ) + m 2 - m 4 - m 5 : ℤ) : ℂ) * ζ := by
    simp only [Fin.sum_univ_six, edgeDir_six, ← hζ]
    have h3 : ζ ^ 3 = -1 := by linear_combination (ζ + 1) * h2
    have h4 : ζ ^ 4 = -ζ := by linear_combination (ζ ^ 2 + ζ) * h2
    have h5 : ζ ^ 5 = 1 - ζ := by linear_combination (ζ ^ 3 + ζ ^ 2 - 1) * h2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    push_cast
    simp only [show ((3 : Fin 6) : ℕ) = 3 from rfl, show ((4 : Fin 6) : ℕ) = 4 from rfl,
      show ((5 : Fin 6) : ℕ) = 5 from rfl]
    linear_combination (m 2 : ℂ) * h2 + (m 3 : ℂ) * h3 + (m 4 : ℂ) * h4 + (m 5 : ℂ) * h5
  rw [hsum, hζ, edgeDir_six_one]
  simp [hexCloses, dot, hexCos, hexSin, List.ofFn_succ, Complex.ext_iff]
  rw [← Int.cast_eq_zero (α := ℝ), ← Int.cast_eq_zero (α := ℝ)]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The OEIS example `t = d = 1`, sides `(1, 6, 2, 4, 3, 5)` counterclockwise, is an
equiangular hexagon in the sense of `IsEquiangularPolygon`. -/
example : IsEquiangularPolygon 6 (fun k => 1 + (![0, 5, 1, 3, 2, 4] : Fin 6 → ℕ) k * 1) := by
  refine ⟨by norm_num, fun _ => by positivity, ?_⟩
  rw [hexCloses_iff]
  decide

/-- Conjecture (Robin Garcia, 2012): hexagons are the only simple convex polygons with equal
interior angles whose integer side lengths are the terms `t, t+d, …, t+(N-1)d` (`d ≥ 1`) of an
arithmetic progression, in some order `σ`. -/
def statement : Prop :=
  ∀ (N t d : ℕ), 1 ≤ d → ∀ σ : Equiv.Perm (Fin N),
    IsEquiangularPolygon N (fun k => t + (σ k : ℕ) * d) → N = 6

end Math0.Statements.A215010
