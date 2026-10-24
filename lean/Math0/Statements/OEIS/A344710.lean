/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A344710: smallest non-obtuse lattice triangles with no side shorter than √n

Source: https://oeis.org/A344710, _Jonathan F. Waldmann_, May 26 2021. Verbatim (FORMULA
section):
> a(n) > sqrt(3/4)*n (conjectured).

The entry's name: "a(n)/2 is the smallest possible area of a non-obtuse triangle with coordinates
in Z^2 and no side shorter than sqrt(n)." Offset `1`, so the sequence (and the conjecture)
concerns every `n ≥ 1`.

## Encoding

* A lattice triangle is a triple `A, B, C : ℤ × ℤ` of non-collinear points, i.e.
  `det2 A B C = det(B - A, C - A) ≠ 0`. Its area is `|det2 A B C| / 2` (shoelace formula), so
  `a n` is the least value of `|det2 A B C|` over the admissible triangles.
* "No side shorter than `√n`": the three squared side lengths `dist2` are all `≥ n`.
* "Non-obtuse": every angle is at most `90°`. The angle of the triangle at the vertex `V` (with
  other vertices `P`, `Q`) is `≤ 90°` iff `(P - V) · (Q - V) ≥ 0` (`dotAt V P Q`). Theorem
  `nonObtuse_iff` shows this is the criterion of the entry's first comment,
  `2*max{|AB|,|BC|,|CA|} ≤ |AB|+|BC|+|CA|` (squared lengths).
  For `n ≥ 1` this already forces `det2 A B C ≠ 0`, so non-collinearity is not an extra
  restriction there. It is included because a triangle is non-degenerate.
* `areas n` is the set of the values `|det2 A B C|` over admissible triangles, and
  `a n := sInf (areas n)`. The set is nonempty (`areas_nonempty`), so `a n` is its least element
  (`isLeast_a`). That is, `a n` is exactly the sequence as defined in the entry.
* The statement is `√(3/4) * n < a n` (in `ℝ`) for every `n ≥ 1`.

The entry's comment also lists "Conjectured next terms (from the conjectured inequality
a(n) > sqrt(3/4)*n) are a(50,...,64) ?= 45, 48, 48, 52, 55, 55, 55, 55, 55, 56, 56, 56, 56, 56,
56." Those values are guesses derived from the inequality, not a separate conjecture, and are not
formalized here.

## Data check

`a` is not computable as written: the admissible triangles range over all of `ℤ²`, and bounding
their size in terms of the area needs an inequality of the same kind as the conjecture
(`4 det² ≥ 3 |AB|² |AC|²` at the largest angle). That bound is not proved here. The checks
below are therefore of two kinds.

* `a_data_le` (kernel-checked, about `a` itself): `a n ≤` the listed term for all 49 listed
  terms `n = 1, …, 49`. It comes from the computable search `aRegion` via `a_le_aRegion`.
* `aRegion_data` (kernel-checked, about the helper): `aRegion n` equals the listed term for all
  49 listed terms. `aRegion n` is the least `|det2|` over admissible triangles with `A = (0, 0)`,
  `C` in the annulus `n ≤ |P|² ≤ 5n/4 + 2` (`mem_annulus`) and `B` in its first octant
  `0 ≤ y ≤ x`. So no admissible triangle in that region does better (`aRegion_le`). The region
  follows the search described in the entry's comments ("set A to (0,0), and look for B and C in
  the set of points X with sqrt(n) <= |AX| < sqrt(5n/4). Furthermore, B can be assumed to be in
  the first octant"), widened by `2` so that it also covers the `n` that are not sums of two
  squares. That this region always contains an optimal triangle is not proved here.
-/

namespace Math0.Statements.A344710

/-- Twice the signed area of the triangle `A B C`: `det(B - A, C - A)`. -/
def det2 (A B C : ℤ × ℤ) : ℤ := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2)

/-- The squared Euclidean distance between the lattice points `P` and `Q`. -/
def dist2 (P Q : ℤ × ℤ) : ℤ := (P.1 - Q.1) * (P.1 - Q.1) + (P.2 - Q.2) * (P.2 - Q.2)

/-- The dot product `(P - V) · (Q - V)`. The angle `∠PVQ` is at most `90°` iff it is `≥ 0`. -/
def dotAt (V P Q : ℤ × ℤ) : ℤ := (P.1 - V.1) * (Q.1 - V.1) + (P.2 - V.2) * (Q.2 - V.2)

/-- `A B C` is a non-obtuse lattice triangle with no side shorter than `√n`: the points are not
collinear, all three squared side lengths are `≥ n`, and all three angles are `≤ 90°`. -/
def IsValid (n : ℕ) (A B C : ℤ × ℤ) : Prop :=
  det2 A B C ≠ 0 ∧
  (n : ℤ) ≤ dist2 A B ∧ (n : ℤ) ≤ dist2 B C ∧ (n : ℤ) ≤ dist2 C A ∧
  0 ≤ dotAt A B C ∧ 0 ≤ dotAt B C A ∧ 0 ≤ dotAt C A B

instance (n : ℕ) (A B C : ℤ × ℤ) : Decidable (IsValid n A B C) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The non-obtuse condition is the entry's criterion
`2 * max {|AB|², |BC|², |CA|²} ≤ |AB|² + |BC|² + |CA|²`. -/
theorem nonObtuse_iff (A B C : ℤ × ℤ) :
    (0 ≤ dotAt A B C ∧ 0 ≤ dotAt B C A ∧ 0 ≤ dotAt C A B) ↔
      2 * max (dist2 A B) (max (dist2 B C) (dist2 C A)) ≤
        dist2 A B + dist2 B C + dist2 C A := by
  have hA : 2 * dotAt A B C = dist2 A B + dist2 C A - dist2 B C := by
    simp only [dotAt, dist2]; ring
  have hB : 2 * dotAt B C A = dist2 A B + dist2 B C - dist2 C A := by
    simp only [dotAt, dist2]; ring
  have hC : 2 * dotAt C A B = dist2 B C + dist2 C A - dist2 A B := by
    simp only [dotAt, dist2]; ring
  omega

/-- The values `2 * area = |det2 A B C|` of the non-obtuse lattice triangles with no side shorter
than `√n`. -/
def areas (n : ℕ) : Set ℕ :=
  {k | ∃ A B C : ℤ × ℤ, IsValid n A B C ∧ (det2 A B C).natAbs = k}

/-- A344710: `a n / 2` is the smallest possible area of a non-obtuse triangle with coordinates in
`ℤ²` and no side shorter than `√n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf (areas n)

/-- The right isosceles triangle with legs `n + 1` is admissible, so `areas n` is nonempty. -/
theorem areas_nonempty (n : ℕ) : (areas n).Nonempty := by
  have hd : det2 (0, 0) ((n : ℤ) + 1, 0) (0, (n : ℤ) + 1) = ((n : ℤ) + 1) ^ 2 := by
    simp only [det2]; ring
  refine ⟨((n : ℤ) + 1) ^ 2 |>.natAbs, (0, 0), ((n : ℤ) + 1, 0), (0, (n : ℤ) + 1), ?_,
    by rw [hd]⟩
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have h1 : dist2 (0, 0) ((n : ℤ) + 1, 0) = ((n : ℤ) + 1) ^ 2 := by simp only [dist2]; ring
  have h2 : dist2 ((n : ℤ) + 1, 0) (0, (n : ℤ) + 1) = 2 * ((n : ℤ) + 1) ^ 2 := by
    simp only [dist2]; ring
  have h3 : dist2 (0, (n : ℤ) + 1) (0, 0) = ((n : ℤ) + 1) ^ 2 := by simp only [dist2]; ring
  have h4 : dotAt (0, 0) ((n : ℤ) + 1, 0) (0, (n : ℤ) + 1) = 0 := by simp only [dotAt]; ring
  have h5 : dotAt ((n : ℤ) + 1, 0) (0, (n : ℤ) + 1) (0, 0) = ((n : ℤ) + 1) ^ 2 := by
    simp only [dotAt]; ring
  have h6 : dotAt (0, (n : ℤ) + 1) (0, 0) ((n : ℤ) + 1, 0) = ((n : ℤ) + 1) ^ 2 := by
    simp only [dotAt]; ring
  have hsq : (n : ℤ) ≤ ((n : ℤ) + 1) ^ 2 := by nlinarith
  have hpos : 0 < ((n : ℤ) + 1) ^ 2 := by positivity
  simp only [IsValid, hd, h1, h2, h3, h4, h5, h6]
  omega

/-- `a n` is the least element of `areas n`: the definition is a true minimum. -/
theorem isLeast_a (n : ℕ) : IsLeast (areas n) (a n) :=
  ⟨Nat.sInf_mem (areas_nonempty n), fun _ hk => Nat.sInf_le hk⟩

/-! ### Computable search over a bounded region (helper for the data check) -/

/-- The bound on squared distances used by the helper search: `5n/4 + 2`. -/
def bnd (n : ℕ) : ℕ := 5 * n / 4 + 2

/-- The lattice points `P` with `n ≤ |P|² ≤ bnd n` (see `mem_annulus`). Their coordinates lie in
`[-r, r]` with `r = n / 2 + 2`. -/
def annulus (n : ℕ) : List (ℤ × ℤ) :=
  let r : ℕ := n / 2 + 2
  let coords : List ℤ := ((List.range (2 * r + 1)).map fun i : ℕ => (i : ℤ) - r).filter
    fun x => decide (x * x ≤ (bnd n : ℤ))
  (coords.flatMap fun x => coords.map fun y => (x, y)).filter fun P =>
    decide ((n : ℤ) ≤ P.1 * P.1 + P.2 * P.2 ∧ P.1 * P.1 + P.2 * P.2 ≤ bnd n)

theorem mem_annulus (n : ℕ) (P : ℤ × ℤ) :
    P ∈ annulus n ↔ (n : ℤ) ≤ P.1 * P.1 + P.2 * P.2 ∧ P.1 * P.1 + P.2 * P.2 ≤ bnd n := by
  obtain ⟨x, y⟩ := P
  simp only [annulus, List.mem_filter, List.mem_flatMap, List.mem_map, Prod.mk.injEq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    -- every coordinate `t` with `t² ≤ bnd n` satisfies `|t| ≤ n / 2 + 2`, so it is listed
    have hm : (n : ℤ) ≤ 2 * ((n / 2 : ℕ) : ℤ) + 1 := by omega
    have hb : 4 * (bnd n : ℤ) ≤ 5 * n + 8 := by simp only [bnd]; omega
    have bound : ∀ t : ℤ, t * t ≤ (bnd n : ℤ) →
        -((n / 2 + 2 : ℕ) : ℤ) ≤ t ∧ t ≤ ((n / 2 + 2 : ℕ) : ℤ) := by
      intro t ht
      push_cast
      constructor <;> by_contra hc <;> push Not at hc
      · have h3 : ((n / 2 : ℕ) : ℤ) + 3 ≤ -t := by omega
        nlinarith
      · have h3 : ((n / 2 : ℕ) : ℤ) + 3 ≤ t := by omega
        nlinarith
    have hx : x * x ≤ (bnd n : ℤ) := by nlinarith [mul_self_nonneg y]
    have hy : y * y ≤ (bnd n : ℤ) := by nlinarith [mul_self_nonneg x]
    have bx := bound x hx
    have bY := bound y hy
    set r : ℤ := ((n / 2 + 2 : ℕ) : ℤ)
    refine ⟨x, ⟨⟨(x + r).toNat, List.mem_range.mpr (by omega), by omega⟩, hx⟩,
      ⟨y, ⟨⟨(y + r).toNat, List.mem_range.mpr (by omega), by omega⟩, hy⟩, rfl, rfl⟩⟩

/-- The points of `annulus n` in the first octant `0 ≤ y ≤ x`. -/
def octant (n : ℕ) : List (ℤ × ℤ) :=
  (annulus n).filter fun P => decide (0 ≤ P.2 ∧ P.2 ≤ P.1)

/-- The values `|det2|` of the admissible triangles with `A = (0, 0)`, `B ∈ octant n` and
`C ∈ annulus n`. -/
def regionDets (n : ℕ) : List ℕ :=
  (octant n).flatMap fun B => (annulus n).filterMap fun C =>
    if IsValid n (0, 0) B C then some (det2 (0, 0) B C).natAbs else none

theorem mem_regionDets {n k : ℕ} :
    k ∈ regionDets n ↔ ∃ B ∈ octant n, ∃ C ∈ annulus n,
      IsValid n (0, 0) B C ∧ (det2 (0, 0) B C).natAbs = k := by
  simp only [regionDets, List.mem_flatMap, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq]

/-- The least `|det2|` over admissible triangles with `A = (0, 0)`, `B ∈ octant n` and
`C ∈ annulus n` (`0` if there is none). -/
def aRegion (n : ℕ) : ℕ := (regionDets n).min?.getD 0

/-- If the bounded search finds a triangle, its value bounds `a n` from above. -/
theorem a_le_aRegion {n : ℕ} (h : aRegion n ≠ 0) : a n ≤ aRegion n := by
  cases hm : (regionDets n).min? with
  | none => simp [aRegion, hm] at h
  | some m =>
    have hmem := (List.min?_eq_some_iff.mp hm).1
    obtain ⟨B, -, C, -, hv, hk⟩ := mem_regionDets.mp hmem
    rw [aRegion, hm, Option.getD_some]
    exact Nat.sInf_le ⟨(0, 0), B, C, hv, hk⟩

/-- No admissible triangle in the search region beats `aRegion n`. -/
theorem aRegion_le {n : ℕ} {B C : ℤ × ℤ} (hB : B ∈ octant n) (hC : C ∈ annulus n)
    (hv : IsValid n (0, 0) B C) : aRegion n ≤ (det2 (0, 0) B C).natAbs := by
  have hmem : (det2 (0, 0) B C).natAbs ∈ regionDets n :=
    mem_regionDets.mpr ⟨B, hB, C, hC, hv, rfl⟩
  cases hm : (regionDets n).min? with
  | none => simp [List.min?_eq_none_iff] at hm; simp [hm] at hmem
  | some m =>
    rw [aRegion, hm, Option.getD_some]
    exact (List.min?_eq_some_iff.mp hm).2 _ hmem

/-- The 49 terms listed in OEIS (`n = 1, …, 49`). -/
def data : List ℕ :=
  [1, 2, 4, 4, 5, 8, 8, 8, 9, 10, 12, 12, 12, 15, 15, 15, 15, 18, 20, 20, 23, 23, 23, 23, 23,
    24, 28, 28, 28, 30, 30, 30, 30, 30, 34, 34, 34, 38, 38, 38, 39, 42, 42, 42, 42, 45, 45, 45,
    45]

/-- The bounded search reproduces all 49 terms listed in OEIS (kernel-checked). -/
theorem aRegion_data : (List.range 49).map (fun i => aRegion (i + 1)) = data := by
  decide +kernel

/-- `a n` is at most the listed term, for all 49 terms listed in OEIS. -/
theorem a_data_le : ∀ i < 49, a (i + 1) ≤ data.getD i 0 := by
  intro i hi
  have h := congrArg (fun l => l.getD i 0) aRegion_data
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some] at h
  rw [List.getD_eq_getElem?_getD, ← h]
  exact a_le_aRegion (by rw [h]; interval_cases i <;> decide)

/-- Conjecture (Waldmann, A344710): `a(n) > √(3/4) * n` for every `n ≥ 1`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → Real.sqrt (3 / 4) * (n : ℝ) < (a n : ℝ)

end Math0.Statements.A344710
