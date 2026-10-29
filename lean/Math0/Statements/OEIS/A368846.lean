/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A368846: Luschny's diagonal sums of the Bernoulli triangle and A229580

Source: https://oeis.org/A368846, Peter Luschny, Jan 07 2024 (COMMENTS section). Verbatim:
> Conjecture: |Sum_{j=0..k} T(k + j, k)| = A229580(k + 1) for k >= 0.

The entry (offset `0`, keywords `sign,tabl`) is "Triangle read by rows: T(n, k) = (-1)^(n + k)*2*
binomial(2*k - 1, n)* binomial(2*n + 1, 2*k) for k > 0, and k^n for k = 0." The referenced
sequence A229580 (R. H. Hardin, Sep 26 2013, offset `1`) is "Number of defective 3-colorings of an
n X 2 0..2 array connected horizontally and antidiagonally with exactly one mistake, and colors
introduced in row-major 0..2 order."

## Encoding

* *The triangle.* `T n k : ℤ` is the displayed formula, with `ℕ`-valued binomials cast to `ℤ`.
  For `k > 0` the factor `2*k - 1` is a natural number (`k ≥ 1`), so truncated subtraction is
  harmless. For `k = 0` the value is `k^n = 0^n` (so `T 0 0 = 1` and `T n 0 = 0` for `n > 0`).
  The formula is used for all `n, k`; the conjecture only evaluates `T (k + j) k` with
  `k ≤ k + j`, i.e. inside the triangle `0 ≤ k ≤ n`.
* *The sequence.* `a` is the triangle read by rows (the OEIS sequence itself, offset `0`); rows
  `0, …, i` hold at least `i + 1` entries, so the `i`-th entry of the concatenation lies among
  them. `a_data` checks all 55 listed terms (rows `0, …, 9`) in the kernel.
* *A229580.* An `n X 2` array has `n` rows and `2` columns (as in the examples of A229580, which
  show `3` rows of `2` entries for `n = 3`). A cell is `(i, j) : Fin n × Fin 2` (row `i`, column
  `j`), and a 0..2 coloring is a map `c : Fin n × Fin 2 → Fin 3`. The connections are
  horizontal, `(i, 0)–(i, 1)`, and antidiagonal, `(i, 1)–(i + 1, 0)`; `IsEdge p q` lists each
  such edge exactly once, as the ordered pair `(p, q)` in which `p` comes first in row-major
  order. A *mistake* is an edge whose two ends have the same color; `mistakes c` counts them.
  *Colors introduced in row-major 0..2 order* (`ColorsInOrder c`): writing `rank (i, j) =
  2 i + j` for the row-major position, every cell of nonzero color `t` is preceded (in row-major
  order) by some cell of color `t - 1`. Equivalently the row-major color word is a restricted
  growth word: it starts with `0`, and each color first appears only after all smaller colors
  have appeared; this picks one coloring from each orbit under permutations of the colors.
  `A229580 n` is the number of colorings with exactly one mistake and colors introduced in this
  order. `A229580_data` checks `A229580 1, A229580 2, A229580 3 = 1, 6, 40` (the first three
  listed terms) in the kernel; larger `n` enumerate `3^(2n)` maps and are too slow.
* *The conjecture.* `statement`: for every `k ≥ 0`,
  `|∑_{j=0}^{k} T(k + j, k)| = A229580(k + 1)`, computed in `ℤ`.
* *Sanity checks* (of the transcription, not a proof): `sum_data` evaluates the left-hand side
  for `k = 0, …, 21` and finds the 22 terms listed in A229580, and `statement_check` confirms
  the conjecture with the definition `A229580` for `k = 0, 1, 2`.
-/

namespace Math0.Statements.A368846

/-! ### The triangle A368846 -/

/-- The triangle of A368846: `T(n, k) = (-1)^(n + k) * 2 * binomial(2k - 1, n) *
binomial(2n + 1, 2k)` for `k > 0`, and `T(n, 0) = k^n = 0^n`. -/
def T (n k : ℕ) : ℤ :=
  if k = 0 then 0 ^ n
  else (-1) ^ (n + k) * 2 * ((2 * k - 1).choose n : ℤ) * ((2 * n + 1).choose (2 * k) : ℤ)

/-- A368846 as a sequence (offset `0`): the triangle `T` (`0 ≤ k ≤ n`) read by rows. -/
def a (i : ℕ) : ℤ :=
  ((List.range (i + 1)).flatMap fun n => (List.range (n + 1)).map (T n)).getD i 0

/-- The definition reproduces all 55 terms listed in OEIS, `a 0, …, a 54` (kernel-checked). -/
theorem a_data : (List.range 55).map (fun i => a (i + 0)) =
    [1, 0, 6, 0, 0, 30, 0, 0, -70, 140, 0, 0, 0, -840, 630, 0, 0, 0, 924, -6930, 2772, 0, 0, 0,
      0, 18018, -48048, 12012, 0, 0, 0, 0, -12870, 216216, -300300, 51480, 0, 0, 0, 0, 0,
      -350064, 2042040, -1750320, 218790, 0, 0, 0, 0, 0, 184756, -5542680, 16628040, -9699690,
      923780] := by
  decide +kernel

/-! ### A229580: defective 3-colorings of the `n X 2` array -/

/-- A cell `(i, j)` of the `n X 2` array: row `i < n`, column `j < 2`. -/
abbrev Cell (n : ℕ) := Fin n × Fin 2

/-- The row-major position of the cell `(i, j)`: `2 i + j`. -/
def Cell.rank {n : ℕ} (p : Cell n) : ℕ := 2 * p.1.val + p.2.val

/-- The connections of the array: horizontal `(i, 0)–(i, 1)` and antidiagonal
`(i, 1)–(i + 1, 0)`. Each edge is listed once, as the ordered pair `(p, q)` with `p` first in
row-major order. -/
def IsEdge {n : ℕ} (p q : Cell n) : Prop :=
  (p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 1) ∨ (p.1.val + 1 = q.1.val ∧ p.2 = 1 ∧ q.2 = 0)

instance {n : ℕ} : DecidableRel (IsEdge (n := n)) := fun p q => by
  unfold IsEdge; infer_instance

/-- The number of mistakes of a coloring: edges whose two ends have the same color. -/
def mistakes {n : ℕ} (c : Cell n → Fin 3) : ℕ :=
  (Finset.univ.filter fun e : Cell n × Cell n => IsEdge e.1 e.2 ∧ c e.1 = c e.2).card

/-- Colors are introduced in row-major `0..2` order: every cell of nonzero color `t` is preceded,
in row-major order, by a cell of color `t - 1`. -/
def ColorsInOrder {n : ℕ} (c : Cell n → Fin 3) : Prop :=
  ∀ p : Cell n, c p ≠ 0 → ∃ q : Cell n, q.rank < p.rank ∧ (c q).val + 1 = (c p).val

instance {n : ℕ} : DecidablePred (ColorsInOrder (n := n)) := fun c => by
  unfold ColorsInOrder; infer_instance

/-- A229580(n): the number of 0..2 colorings of the `n X 2` array, connected horizontally and
antidiagonally, with exactly one mistake and colors introduced in row-major `0..2` order. -/
def A229580 (n : ℕ) : ℕ :=
  (Finset.univ.filter fun c : Cell n → Fin 3 => mistakes c = 1 ∧ ColorsInOrder c).card

/-- The definition of A229580 reproduces its first three listed terms (kernel-checked). -/
theorem A229580_data : (List.range 3).map (fun i => A229580 (i + 1)) = [1, 6, 40] := by
  decide +kernel

/-! ### The conjecture -/

/-- Sanity check: `|∑_{j=0}^{k} T(k + j, k)|` for `k = 0, …, 21` are the 22 terms of A229580
listed in OEIS (kernel-checked). -/
theorem sum_data : (List.range 22).map (fun k => |∑ j ∈ Finset.range (k + 1), T (k + j) k|) =
    [1, 6, 40, 224, 1152, 5632, 26624, 122880, 557056, 2490368, 11010048, 48234496, 209715200,
      905969664, 3892314112, 16642998272, 70866960384, 300647710720, 1271310319616,
      5360119185408, 22539988369408, 94557999988736] := by
  decide +kernel

/-- Luschny's conjecture: for every `k ≥ 0`, the absolute value of the `k`-th column sum
`∑_{j=0}^{k} T(k + j, k)` of the triangle A368846 equals A229580(k + 1). -/
def statement : Prop :=
  ∀ k : ℕ, |∑ j ∈ Finset.range (k + 1), T (k + j) k| = (A229580 (k + 1) : ℤ)

/-- Sanity check of the transcription: the conjecture holds for `k = 0, 1, 2` (kernel-checked;
this is not a proof of `statement`). -/
theorem statement_check :
    ∀ k < 3, |∑ j ∈ Finset.range (k + 1), T (k + j) k| = (A229580 (k + 1) : ℤ) := by
  decide +kernel

end Math0.Statements.A368846
