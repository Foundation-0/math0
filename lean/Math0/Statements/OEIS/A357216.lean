/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A357216: regions in a regular n-gon cut by k internal n-gons

Source: https://oeis.org/A357216, _Scott R. Shannon_, Sep 18 2022. Verbatim (COMMENTS and
FORMULA sections):
> Conjecture: the only n-gons that contain non-simple intersections are the 3-gon (triangle),
> 4-gon (square), and 6-gon (hexagon).

> Conjectured formula for all columns for n >= 7: T(n,k) = n*k^2 + 1.

> Conjectured formula for all rows except for n = 3, 4, 6: T(n,k) = n*k^2 + 1.

The entry's definition: "Table read by antidiagonals: T(n,k) (n >= 3, k >= 0) is the number of
regions in an n-gon when k internal n-gons are drawn between the n*k points that divide each side
into k+1 equal parts." (offset 3).

## Encoding

*Geometry (used by `statement`).* The plane is `ℂ`. The regular `n`-gon has vertices
`vertex n j = exp (2πij/n)`, `j = 0, …, n-1` (`vertex n n = vertex n 0`); side `j` runs from
`vertex n j` to `vertex n (j+1)`. Its `m`-th division point (`m = 1, …, k`) is
`divPt n k j m = V_j + m/(k+1) (V_{j+1} - V_j)`. The `m`-th internal `n`-gon joins the `m`-th
division points of consecutive sides, so its sides are the segments
`chord n k (j, m-1) = [divPt n k j m, divPt n k (j+1) m]` (indexed by `Fin n × Fin k`). Each
internal `n`-gon is then a rotated and scaled copy of the outer one; this reading reproduces the
data (see below). The regions are the connected components of the interior of the
outer polygon with all `n*k` chords removed: `regions n k = Nat.card (ConnectedComponents …)`.
(The sides of the outer polygon are its frontier, removed by taking the interior.)

A *non-simple intersection* is a point where three or more of the drawn lines meet, i.e. a point
lying on at least three distinct chords (`HasNonSimpleIntersection`). The division points
themselves are not counted: there only two chords meet (together with a side of the outer
polygon), for every `n` and `k`. A point on three distinct chords can only be an interior point
(the relative interior of each chord lies in the open polygon, and the endpoints of the chords
are the division points, each the endpoint of exactly two chords), so no further restriction is
needed.

*Reading of the conjecture.* "The only n-gons that contain non-simple intersections are the
3-gon, 4-gon and 6-gon" is read as: for `n ≥ 3`, some `k` gives a non-simple intersection iff
`n ∈ {3, 4, 6}` (they occur first at `k = 5`, `5`, `9` respectively: the data give
`T(3,5) = 70 < 76`, `T(4,5) = 93 < 101`, `T(6,9) = 475 < 487`). The two conjectured formulas
together say `T(n,k) = n*k^2 + 1` for `n = 5` and every `n ≥ 7`, for all `k ≥ 0` (the table's
range of `k`). `statement` is the conjunction of these two claims.

*The computable table `T`.* The count is computed exactly; the link `T n k = regions n k` is
the intended meaning and is not proved here.
* Coordinates. With `ζ = exp (2πi/n)` and `c = ζ + 1/ζ = 2 cos (2π/n)`, the map
  `(x, y) ↦ x + y ζ` is an `ℝ`-linear bijection `ℝ² → ℂ`, so it preserves incidences. Since
  `ζ^2 = c ζ - 1`, every `ζ^j` is `A_j(c) + B_j(c) ζ` with integer polynomials `A_j, B_j`
  (`zpow`), and all coordinates of the division points (scaled by `k+1`, `divPtC`) lie in
  `ℤ[c] ≅ ℤ[t]/(ψ_n)`. Here `ψ_n` (`psi`) is the minimal polynomial of `c`, obtained from the
  palindromic cyclotomic polynomial `Φ_n` (`cycloBE`, computed by exact division of `x^n - 1` by
  the `Φ_d`, `d ∣ n`, `d < n`) via `x^(-D) Φ_n(x) = ψ_n(x + 1/x)`. Elements of `ℤ[c]` are kept
  reduced modulo `ψ_n`, so an element is `0` iff its reduced coefficient list is `0`.
* Counting. For chords whose endpoints lie on the boundary of a convex polygon (here: in the
  relative interiors of two different sides), adding the chords one at a time, a chord splits as
  many regions as the number of pieces it is cut into, i.e. `1 +` the number of distinct points
  of the open chord lying on earlier chords. Add the chords in order of `m`. Two sides of the same
  internal `n`-gon meet only at its vertices, on the boundary, so the earlier chords meeting
  chord `(j, m)` inside the polygon are chords `(j', m')` with `m' < m`. The rotation by `2π/n`
  maps the drawing onto itself and chord `(j, m)` to `(j+1, m)`. Hence
  `T(n,k) = 1 + n * ∑_{m=1}^{k} (1 + E_m)`, where `E_m` (`newPoints`) is the number of distinct
  points in which chord `(0, m)` meets the chords `(j', m')`, `m' < m`.
* Crossings. Two chords meet in the open polygon iff their four endpoints are distinct and
  interleave along the boundary of the convex polygon (`crosses`; the `m`-th division point of
  side `j` has boundary position `j*(k+1)+m`). Chords sharing an endpoint meet only there: three
  points in the relative interiors of three distinct sides of a convex polygon are never
  collinear.
* Distinct meeting points. The chord `(j', m')` on the line `a x + b y = e` (`chordLine`) meets
  chord `(0, m)`, from `P` to `Q`, at `P + λ (Q - P)` with `λ = num / den`,
  `num = e - a P_x - b P_y`, `den = a (Q - P)_x + b (Q - P)_y ≠ 0` (`meetParam`). Two such points
  coincide iff `num₁ den₂ - num₂ den₁ = 0` in `ℤ[c]` (`countDistinct`).

A Python transcription of `T`, and of a second exact variant that sums over all chords in the
cyclotomic ring `ℤ[ζ]` without the symmetry reduction, reproduces all 195 values of the entry's
EXAMPLE table (`n = 3..15`, `k = 0..14`). An independent floating-point computation (orientation
tests for crossings, clustering of intersection points) reproduces the 66 listed terms, and the
crossing criterion agrees with floating-point orientation tests for `n ≤ 20`, `k ≤ 15`.

*Sequence indexing.* `a` reads the table by antidiagonals (`a 3 = T(3,0)`, `a 4 = T(3,1)`,
`a 5 = T(4,0)`, …), indexed from the entry's offset `3`; `a_data` checks all 66 listed terms
(antidiagonals `n + k = 3, …, 13`).
-/

namespace Math0.Statements.A357216

/-! ### The geometric definition -/

/-- The `j`-th vertex `exp (2πij/n)` of the regular `n`-gon inscribed in the unit circle. -/
noncomputable def vertex (n j : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * j / n)

/-- The `m`-th of the `k` points dividing side `j` (from `vertex n j` to `vertex n (j+1)`)
into `k+1` equal parts. -/
noncomputable def divPt (n k j m : ℕ) : ℂ :=
  vertex n j + ((m : ℂ) / ((k : ℂ) + 1)) * (vertex n (j + 1) - vertex n j)

/-- Side `c.1` of the internal `n`-gon number `c.2 + 1`: the segment joining the
`(c.2+1)`-th division points of sides `c.1` and `c.1 + 1`. -/
noncomputable def chord (n k : ℕ) (c : Fin n × Fin k) : Set ℂ :=
  segment ℝ (divPt n k (c.1 : ℕ) ((c.2 : ℕ) + 1)) (divPt n k ((c.1 : ℕ) + 1) ((c.2 : ℕ) + 1))

/-- The (closed) regular `n`-gon. -/
noncomputable def polygon (n : ℕ) : Set ℂ :=
  convexHull ℝ (Set.range fun j : Fin n => vertex n j)

/-- The interior of the `n`-gon with the sides of all `k` internal `n`-gons removed. -/
noncomputable def regionSet (n k : ℕ) : Set ℂ :=
  interior (polygon n) \ ⋃ c : Fin n × Fin k, chord n k c

/-- `T(n,k)` as defined in the entry: the number of regions (connected components) into which
the `k` internal `n`-gons cut the regular `n`-gon. -/
noncomputable def regions (n k : ℕ) : ℕ :=
  Nat.card (ConnectedComponents (regionSet n k))

/-- The drawing for `(n, k)` has a non-simple intersection: some point lies on three distinct
sides of the internal `n`-gons. -/
def HasNonSimpleIntersection (n k : ℕ) : Prop :=
  ∃ p : ℂ, ∃ c₁ c₂ c₃ : Fin n × Fin k, c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧
    p ∈ chord n k c₁ ∧ p ∈ chord n k c₂ ∧ p ∈ chord n k c₃

/-! ### The exact computation

Little-endian lists are integer polynomials (`[c₀, c₁, …] = c₀ + c₁ t + …`); `BE` functions work
on big-endian lists (leading coefficient first). -/

/-- Sum of polynomials. -/
def padd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: padd p q

/-- Negation of a polynomial. -/
def pneg (p : List ℤ) : List ℤ := p.map fun a => -a

/-- Difference of polynomials. -/
def psub (p q : List ℤ) : List ℤ := padd p (pneg q)

/-- Scalar multiple of a polynomial. -/
def psmul (c : ℤ) (p : List ℤ) : List ℤ := p.map fun a => c * a

/-- Product of polynomials. -/
def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => padd (psmul a q) (0 :: pmul p q)

/-- Coefficientwise difference of big-endian lists aligned at the leading end. -/
def subFront : List ℤ → List ℤ → List ℤ
  | p, [] => p
  | [], q => pneg q
  | a :: p, b :: q => (a - b) :: subFront p q

/-- One step of long division by the monic big-endian divisor `1 :: qs`. -/
def cancelLead (qs : List ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: p => subFront p (psmul a qs)

/-- Remainder of `p` modulo the monic `q` (big-endian; `fuel ≥ p.length` suffices). -/
def remBE (q : List ℤ) : ℕ → List ℤ → List ℤ
  | 0, p => p
  | fuel + 1, p => if q.length ≤ p.length then remBE q fuel (cancelLead q.tail p) else p

/-- Quotient of `p` by the monic `q` (big-endian; `fuel ≥ p.length` suffices). -/
def quotBE (q : List ℤ) : ℕ → List ℤ → List ℤ
  | 0, _ => []
  | fuel + 1, p =>
    if q.length ≤ p.length then p.headD 0 :: quotBE q fuel (cancelLead q.tail p) else []

/-- `x ^ n - 1`, big-endian (`n ≥ 1`). -/
def xPowSubOneBE (n : ℕ) : List ℤ := 1 :: List.replicate (n - 1) 0 ++ [-1]

/-- The cyclotomic polynomial `Φ_n = (x^n - 1) / ∏_{d ∣ n, d < n} Φ_d`, big-endian. -/
def cycloBE : ℕ → ℕ → List ℤ
  | 0, _ => [1]
  | fuel + 1, n =>
    (List.range n).foldl
      (fun acc d => if 0 < d ∧ n % d = 0 then quotBE (cycloBE fuel d) acc.length acc else acc)
      (xPowSubOneBE n)

/-- `∑ a_i D_i` for the Dickson polynomials `D_{i+1} = t D_i - D_{i-1}`, starting from
`acc` with the current pair `(D_{i-1}, D_i)`. -/
def dicksonSum : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ
  | acc, _, _, [] => acc
  | acc, Dp, Dc, a :: as => dicksonSum (padd acc (psmul a Dc)) Dc (psub (0 :: Dc) Dp) as

/-- The minimal polynomial `ψ_n` of `2 cos (2π/n)` (`n ≥ 3`), little-endian. Writing the
palindromic `Φ_n(x) = ∑_{i ≤ 2D} a_i x^i`, we have
`ψ_n(x + 1/x) = x^(-D) Φ_n(x) = a_D + ∑_{i=1}^{D} a_{D+i} D_i(x + 1/x)`. -/
def psi (n : ℕ) : List ℤ :=
  let cyc := cycloBE n n
  dicksonSum [cyc.getD (cyc.length / 2) 0] [2] [0, 1] (cyc.drop (cyc.length / 2 + 1))

/-- Reduction of a little-endian polynomial modulo the monic big-endian `q`. -/
def red (q p : List ℤ) : List ℤ := (remBE q p.length p.reverse).reverse

/-- Zero test for a reduced element. -/
def isZero (p : List ℤ) : Bool := p.all (· == 0)

/-- Coordinates `(A_j, B_j)` of `ζ^j = A_j + B_j ζ`, as polynomials in `c = ζ + 1/ζ` reduced
modulo `q = ψ_n` (big-endian), from `ζ^2 = c ζ - 1`. -/
def zpow (q : List ℤ) : ℕ → List ℤ × List ℤ
  | 0 => ([1], [])
  | j + 1 => match zpow q j with
    | (a, b) => (pneg b, red q (padd a (0 :: b)))

/-- `(k+1)` times the `m`-th division point of side `j`, in coordinates. -/
def divPtC (q : List ℤ) (k j m : ℕ) : List ℤ × List ℤ :=
  match zpow q j, zpow q (j + 1) with
  | (a, b), (a', b') =>
    (padd (psmul ((k + 1 - m : ℕ) : ℤ) a) (psmul (m : ℤ) a'),
     padd (psmul ((k + 1 - m : ℕ) : ℤ) b) (psmul (m : ℤ) b'))

/-- The line `a x + b y = e` through `(k+1) P_{j,m}` and `(k+1) P_{j+1,m}`. -/
def chordLine (q : List ℤ) (k j m : ℕ) : List ℤ × List ℤ × List ℤ :=
  match divPtC q k j m, divPtC q k (j + 1) m with
  | (x₁, y₁), (x₂, y₂) =>
    (psub y₁ y₂, psub x₂ x₁, red q (padd (pmul (psub y₁ y₂) x₁) (pmul (psub x₂ x₁) y₁)))

/-- Boundary positions of the two endpoints of chord `(j, m)`. -/
def endpoints (n k : ℕ) (c : ℕ × ℕ) : ℕ × ℕ :=
  (c.1 * (k + 1) + c.2, ((c.1 + 1) % n) * (k + 1) + c.2)

/-- `x` lies strictly between `a` and `b`. -/
def strictlyBetween (a b x : ℕ) : Bool := (a < x && x < b) || (b < x && x < a)

/-- Chords `c` and `e` meet inside the polygon: their endpoints are distinct and interleave
along the boundary. -/
def crosses (n k : ℕ) (c e : ℕ × ℕ) : Bool :=
  match endpoints n k c, endpoints n k e with
  | (a, b), (x, y) =>
    a != x && a != y && b != x && b != y && (strictlyBetween a b x != strictlyBetween a b y)

/-- The parameter `num / den` along chord `(0, m)` (scaled by `k+1`, from `(k+1) P_{0,m}` to
`(k+1) P_{1,m}`) of its meeting point with the line `L`. -/
def meetParam (q : List ℤ) (k m : ℕ) (L : List ℤ × List ℤ × List ℤ) : List ℤ × List ℤ :=
  match divPtC q k 0 m, divPtC q k 1 m, L with
  | (x₁, y₁), (x₂, y₂), (a, b, e) =>
    (red q (psub e (padd (pmul a x₁) (pmul b y₁))),
     red q (padd (pmul a (psub x₂ x₁)) (pmul b (psub y₂ y₁))))

/-- Number of distinct parameters `num / den` in the list (all `den ≠ 0`). -/
def countDistinct (q : List ℤ) : List (List ℤ × List ℤ) → List (List ℤ × List ℤ) → ℕ
  | _, [] => 0
  | seen, p :: ps =>
    (if seen.any (fun p' => isZero (red q (psub (pmul p.1 p'.2) (pmul p'.1 p.2)))) then 0 else 1)
      + countDistinct q (p :: seen) ps

/-- `E_m`: the number of distinct points in which chord `(0, m)` meets chords `(j, m')`
with `m' < m`. -/
def newPoints (n k : ℕ) (q : List ℤ) (m : ℕ) : ℕ :=
  countDistinct q []
    (((List.range (m - 1)).flatMap fun m' => (List.range n).map fun j => (j, m' + 1)).filter
        (fun c => crosses n k (0, m) c) |>.map fun c => meetParam q k m (chordLine q k c.1 c.2))

/-- `T(n,k)` computed exactly: `1 + n * ∑_{m=1}^{k} (1 + E_m)` (see the module docstring). -/
def T (n k : ℕ) : ℕ :=
  let q := (psi n).reverse
  1 + n * ((List.range k).map fun m => 1 + newPoints n k q (m + 1)).sum

/-- `antidiagPos i = (d, r)`: the `i`-th term (from `0`) of a table read by antidiagonals is
term `r` (from `0`) of antidiagonal `d`. -/
def antidiagPos : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | i + 1 => match antidiagPos i with
    | (d, r) => if r < d then (d, r + 1) else (d + 1, 0)

/-- A357216 as a sequence (offset 3): the table `T(n,k)` (`n ≥ 3`, `k ≥ 0`) read by
antidiagonals, `T(3,0), T(3,1), T(4,0), T(3,2), T(4,1), T(5,0), …`. -/
def a (i : ℕ) : ℕ :=
  match antidiagPos (i - 3) with
  | (d, r) => T (3 + r) (d - r)

/-- The definition reproduces all 66 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 66).map (fun i => a (i + 3)) =
    [1, 4, 1, 13, 5, 1, 28, 17, 6, 1, 49, 37, 21, 7, 1, 70, 65, 46, 25, 8, 1, 109, 93, 81, 55,
     29, 9, 1, 148, 145, 126, 97, 64, 33, 10, 1, 181, 181, 181, 151, 113, 73, 37, 11, 1, 244,
     257, 246, 217, 176, 129, 82, 41, 12, 1, 301, 309, 321, 295, 253, 201, 145, 91, 45, 13,
     1] := by
  decide +kernel

/-- Conjecture (Scott R. Shannon, 2022): among the regular `n`-gons (`n ≥ 3`) cut by `k`
internal `n`-gons, exactly the triangle, the square and the hexagon have (for some `k`) a point
on three or more of the drawn lines; and for `n = 5` and every `n ≥ 7` the number of regions is
`T(n,k) = n*k^2 + 1` for all `k ≥ 0`. -/
def statement : Prop :=
  (∀ n : ℕ, 3 ≤ n → ((∃ k : ℕ, HasNonSimpleIntersection n k) ↔ (n = 3 ∨ n = 4 ∨ n = 6))) ∧
  (∀ n k : ℕ, (n = 5 ∨ 7 ≤ n) → regions n k = n * k ^ 2 + 1)

end Math0.Statements.A357216
