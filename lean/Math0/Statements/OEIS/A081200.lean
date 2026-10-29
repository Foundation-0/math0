/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A081200: collinear 5-point subsets of the `5 × 5 × ⋯ × 5` grid

Source: https://oeis.org/A081200, Ron Hardin, May 24 2010 (COMMENTS section). Verbatim:
> Conjecture (verified up to a(9)): Number of collinear 5-tuples of points in a 5 X 5 X 5 X ...
> n-dimensional cubic grid.

The sequence (offset `0`, by Paul Barry) is defined as "6th binomial transform of
(0,1,0,1,0,1,...), A000035."

## Encoding

* The `m`-th binomial transform of a sequence `b` is, in the OEIS convention,
  `n ↦ ∑_{k=0}^{n} C(n,k) m^(n-k) b(k)` (`binomialTransform`). A000035 is `k ↦ k mod 2`
  (offset `0`: `0, 1, 0, 1, …`). So `a n = ∑_{k=0}^{n} C(n,k) 6^(n-k) (k mod 2)`, exactly the
  OEIS definition (not one of the closed forms such as `(7^n - 5^n)/2`). `a_data` checks all 23
  listed terms `a 0, …, a 22` in the kernel.
* The `n`-dimensional `5 × 5 × ⋯ × 5` cubic grid is `Fin n → Fin 5`, i.e. `{0, …, 4}^n`, sitting
  in `ℝ^n = Fin n → ℝ` via `toReal` (coordinatewise inclusion `Fin 5 → ℕ → ℝ`).
* "Collinear 5-tuples of points" are read as unordered 5-element sets of grid points: a
  `Finset` `s` of grid points with `s.card = 5` whose image in `ℝ^n` is collinear in Mathlib's
  sense (`Collinear ℝ`, i.e. its vector span has dimension at most `1`, i.e. all its points lie
  on one real line). Unordered sets is the only reading consistent with the data
  (`a 1 = 1`: the one-dimensional grid has exactly one 5-element subset; ordered 5-tuples
  of distinct points would give `120`).
* The count is `Set.ncard` of the (finite) set of such `s`.
* Range of `n`: the conjecture is a claim about the sequence, whose offset is `0`, so it is stated
  for every `n : ℕ`. (For `n = 0` the grid is a single point, there are no 5-element subsets,
  and `a 0 = 0`; for `n ≥ 1` it is the `n`-dimensional grid.)
-/

namespace Math0.Statements.A081200

/-- The `m`-th binomial transform of a sequence `b` (OEIS convention):
`n ↦ ∑_{k=0}^{n} C(n,k) m^(n-k) b(k)`. -/
def binomialTransform (m : ℕ) (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * m ^ (n - k) * b k

/-- A000035: `k mod 2`, i.e. `0, 1, 0, 1, …` (offset `0`). -/
def A000035 (k : ℕ) : ℕ := k % 2

/-- A081200: the 6th binomial transform of `(0, 1, 0, 1, 0, 1, …)` (A000035). -/
def a (n : ℕ) : ℕ := binomialTransform 6 A000035 n

/-- The definition reproduces all 23 terms listed in OEIS, `a 0, …, a 22` (kernel-checked). -/
theorem a_data : (List.range 23).map (fun i => a (i + 0)) =
    [0, 1, 12, 109, 888, 6841, 51012, 372709, 2687088, 19200241, 136354812, 964249309,
      6798573288, 47834153641, 336059778612, 2358521965909, 16540171339488, 115933787267041,
      812299450322412, 5689910849522509, 39848449432985688, 279034513462540441,
      1953718431395986212] := by
  decide +kernel

/-- The point of `ℝ^n` with the same coordinates as the grid point `x ∈ {0, …, 4}^n`. -/
def toReal (n : ℕ) (x : Fin n → Fin 5) : Fin n → ℝ := fun i => ((x i : ℕ) : ℝ)

/-- Hardin's conjecture: for every `n`, the number of 5-element sets of points of the
`n`-dimensional `5 × 5 × ⋯ × 5` grid `{0, …, 4}^n` that are collinear (lie on one line of `ℝ^n`)
equals `a n`, the 6th binomial transform of `(0, 1, 0, 1, …)`. -/
def statement : Prop :=
  ∀ n : ℕ,
    {s : Finset (Fin n → Fin 5) |
        s.card = 5 ∧ Collinear ℝ (toReal n '' (s : Set (Fin n → Fin 5)))}.ncard = a n

end Math0.Statements.A081200
