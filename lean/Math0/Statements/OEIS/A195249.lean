/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A195249: lower triangles of a 3 × 3 array with king-neighbours differing by at most 2

Source: https://oeis.org/A195249, _R. H. Hardin_, Sep 13 2011. Verbatim (FORMULA section):
> Empirical: a(n) = 1047*n - 1459 for n>2.

The entry's name: "Number of lower triangles of a 3 X 3 0..n array with each element differing
from all of its diagonal, vertical, antidiagonal and horizontal neighbors by two or less."
Offset `1`. The same FORMULA section also records, verbatim:
> Conjectures from _Colin Barker_, May 06 2018: (Start)
> G.f.: x*(64 + 601*x + 288*x^2 + 94*x^3) / (1 - x)^2.
> a(n) = 2*a(n-1) - a(n-2) for n>4.
> (End)

## Encoding

* The lower triangle of a 3 × 3 array consists of the six positions `(i, j)` (row `i`, column
  `j`, both in `0, 1, 2`) with `j ≤ i`, i.e. rows of lengths 1, 2, 3, as in the entry's
  examples. They are enumerated as `cell : Fin 6 → ℕ × ℕ`; `image_cell` and `cell_injective`
  check (in the kernel) that `cell` lists each such position exactly once.
* Two positions are diagonal, vertical, antidiagonal or horizontal neighbours (`Adj`) iff they
  are distinct and both their row indices and their column indices differ by at most one. Only
  neighbours inside the triangle are constrained, since the triangle is the whole object being
  counted.
* A triangle is a vector `v : Fin 6 → ℕ` of entries (entry of `cell k` is `v k`); it is valid
  (`Valid`) iff every two neighbouring entries differ by two or less (`near`).
* `a n` is the number of valid triangles with all six entries in `0..n`, written as a six-fold
  sum over `x₀, …, x₅ ∈ {0, …, n}` of the indicator of `Valid ![x₀, …, x₅]`. The OEIS offset is
  `1`; `a 0 = 1` (the all-zero triangle) is not a term of the sequence.
* The kernel cannot afford the `(n+1)^6` loop of `a` for many `n`, so the data check goes through
  a pruned copy `aL` (each entry is only searched within distance `2` of an already chosen
  neighbour, and constraints are tested as early as possible), proved equal to `a` in
  `a_eq_aL`. Independently, `a_small` evaluates `a 1` and `a 2` straight from the definition.
* Hardin's conjecture is `statement`: for every `n > 2`, `a(n) = 1047 n - 1459`, stated in `ℤ`
  (so that no truncated subtraction is involved).
* Barker's two companion conjectures are recorded as `statementBarkerGF` (the g.f. is read as
  `∑_{n ≥ 1} a(n) x^n`, matching the offset `1`, and the identity of power series over `ℤ` is
  stated after clearing the denominator `(1 - x)^2`, which is a unit) and `statementBarkerRec`
  (the recurrence for all `n > 4`, in `ℤ`).
-/

namespace Math0.Statements.A195249

open Finset

/-- The six positions `(row, column)` of the lower triangle of a 3 × 3 array, i.e. the
positions `(i, j)` with `j ≤ i < 3`, listed row by row. -/
def cell : Fin 6 → ℕ × ℕ := ![(0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2)]

/-- Two positions are diagonal, vertical, antidiagonal or horizontal neighbours iff they are
distinct and their rows and their columns each differ by at most one. -/
def Adj (p q : ℕ × ℕ) : Prop :=
  p ≠ q ∧ p.1 ≤ q.1 + 1 ∧ q.1 ≤ p.1 + 1 ∧ p.2 ≤ q.2 + 1 ∧ q.2 ≤ p.2 + 1

/-- `x` and `y` differ by two or less. -/
def near (x y : ℕ) : Prop := x ≤ y + 2 ∧ y ≤ x + 2

instance : DecidableRel near := fun x y => by unfold near; infer_instance

/-- A filling `v` of the lower triangle (`v k` is the entry at position `cell k`) is valid iff
each entry differs from each of its neighbours by two or less. -/
def Valid (v : Fin 6 → ℕ) : Prop := ∀ i j : Fin 6, Adj (cell i) (cell j) → near (v i) (v j)

instance (v : Fin 6 → ℕ) : Decidable (Valid v) := by unfold Valid Adj; infer_instance

/-- A195249: the number of lower triangles of a 3 × 3 array with entries in `0..n` in which each
element differs from all of its diagonal, vertical, antidiagonal and horizontal neighbours by
two or less (offset `1`). -/
def a (n : ℕ) : ℕ :=
  ∑ x0 ∈ range (n + 1), ∑ x1 ∈ range (n + 1), ∑ x2 ∈ range (n + 1), ∑ x3 ∈ range (n + 1),
    ∑ x4 ∈ range (n + 1), ∑ x5 ∈ range (n + 1), if Valid ![x0, x1, x2, x3, x4, x5] then 1 else 0

/-! ### Sanity checks of the encoding -/

/-- `cell` lists distinct positions. -/
theorem cell_injective : Function.Injective cell := by decide

/-- `cell` lists exactly the positions `(i, j)` with `j ≤ i < 3` of a 3 × 3 array. -/
theorem image_cell :
    univ.image cell = (range 3 ×ˢ range 3).filter (fun p => p.2 ≤ p.1) := by decide

/-- The neighbour constraints, made explicit: the ten neighbouring pairs of the triangle are
`0–1, 0–2, 1–2, 1–3, 2–3, 1–4, 2–4, 3–4, 2–5, 4–5` (grouped by their larger index). -/
theorem valid_iff (x0 x1 x2 x3 x4 x5 : ℕ) :
    Valid ![x0, x1, x2, x3, x4, x5] ↔
      (((near x0 x1 ∧ (near x0 x2 ∧ near x1 x2)) ∧ (near x1 x3 ∧ near x2 x3)) ∧
        (near x1 x4 ∧ (near x2 x4 ∧ near x3 x4))) ∧ (near x2 x5 ∧ near x4 x5) := by
  simp only [Valid, Fin.forall_fin_succ, cell, Adj, near]
  simp
  omega

/-- `a 1` and `a 2`, evaluated in the kernel directly from the definition. -/
theorem a_small : a 1 = 64 ∧ a 2 = 729 := by
  decide +kernel

/-! ### A kernel-friendly copy of the definition -/

/-- The values in `0..n` within distance two of `y`, as a list. -/
def win (n y : ℕ) : List ℕ := List.range' (y - 2) (min (y + 2) n + 1 - (y - 2))

/-- `∑_{x ∈ l} f x` for a list `l`. -/
def lsum (l : List ℕ) (f : ℕ → ℕ) : ℕ := l.foldr (fun x acc => f x + acc) 0

/-- Pruned copy of `a`: each entry is searched near an already chosen neighbour. -/
def aL (n : ℕ) : ℕ :=
  lsum (List.range (n + 1)) fun x0 =>
  lsum (win n x0) fun x1 =>
  lsum (win n x0) fun x2 => if near x1 x2 then
  lsum (win n x1) fun x3 => if near x2 x3 then
  lsum (win n x1) fun x4 => if near x2 x4 ∧ near x3 x4 then
  lsum (win n x2) fun x5 => if near x4 x5 then 1 else 0
  else 0 else 0 else 0

theorem lsum_eq (l : List ℕ) (f : ℕ → ℕ) : lsum l f = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, List.sum_cons, ← ih]; rfl

theorem sum_range_eq_lsum (m : ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ range m, f x = lsum (List.range m) f := by
  rw [lsum_eq]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem filter_near (n y : ℕ) :
    (range (n + 1)).filter (fun x => near y x) = Icc (y - 2) (min (y + 2) n) := by
  ext x
  rw [mem_filter, mem_range, mem_Icc]
  unfold near
  omega

theorem sum_win (n y : ℕ) (g : ℕ → ℕ) :
    ∑ x ∈ range (n + 1), (if near y x then g x else 0) = lsum (win n y) g := by
  rw [← sum_filter, filter_near, Nat.Icc_eq_range', lsum_eq, win]
  rfl

theorem sum_win_and (n y : ℕ) (q : ℕ → Prop) [DecidablePred q] (g : ℕ → ℕ) :
    ∑ x ∈ range (n + 1), (if near y x ∧ q x then g x else 0) =
      lsum (win n y) (fun x => if q x then g x else 0) := by
  rw [← sum_win]
  exact sum_congr rfl fun x _ => ite_and _ _ _ _

theorem sum_pull (s : Finset ℕ) (p : Prop) [Decidable p] (q : ℕ → Prop) [DecidablePred q]
    (g : ℕ → ℕ) :
    ∑ x ∈ s, (if p ∧ q x then g x else 0) =
      if p then ∑ x ∈ s, (if q x then g x else 0) else 0 := by
  by_cases hp : p <;> simp [hp]

theorem a_eq_aL (n : ℕ) : a n = aL n := by
  simp only [a, valid_iff, sum_pull, sum_win_and, sum_win]
  rw [sum_range_eq_lsum]
  rfl

/-- The definition reproduces all 38 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 38).map (fun i => a (i + 1)) =
    [64, 729, 1682, 2729, 3776, 4823, 5870, 6917, 7964, 9011, 10058, 11105, 12152, 13199, 14246,
      15293, 16340, 17387, 18434, 19481, 20528, 21575, 22622, 23669, 24716, 25763, 26810, 27857,
      28904, 29951, 30998, 32045, 33092, 34139, 35186, 36233, 37280, 38327] := by
  rw [show a = aL from funext a_eq_aL]
  decide +kernel

/-! ### The conjectures -/

/-- Conjecture (Hardin, A195249, "Empirical"): `a(n) = 1047 n - 1459` for every `n > 2`. -/
def statement : Prop := ∀ n : ℕ, 2 < n → (a n : ℤ) = 1047 * n - 1459

/-- Barker's conjectured generating function: `∑_{n ≥ 1} a(n) x^n =
x (64 + 601 x + 288 x^2 + 94 x^3) / (1 - x)^2`, with the denominator cleared. -/
def statementBarkerGF : Prop :=
  (1 - PowerSeries.X) ^ 2 * PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) =
    PowerSeries.X * (64 + 601 * PowerSeries.X + 288 * PowerSeries.X ^ 2 + 94 * PowerSeries.X ^ 3)

/-- Barker's conjectured recurrence: `a(n) = 2 a(n-1) - a(n-2)` for every `n > 4`. -/
def statementBarkerRec : Prop :=
  ∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)

end Math0.Statements.A195249
