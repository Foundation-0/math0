/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A338885: diagonal lattice rectangles inscribed in an n X k box

Source: https://oeis.org/A338885, _Peter Kagey_, Nov 14 2020. Verbatim:
> Conjecture: The smallest number in the n-th row is A228286(n).

The entry's definition: "Irregular triangle read by rows in which the n-th row lists all numbers
k such that there exists a diagonal lattice rectangle touching all four sides of an n X k
rectangle." and "A diagonal lattice rectangle is a rectangle with integer coordinates and no side
parallel to the x-axis." Rows are indexed from `n = 2` (offset `2`), and A228286 (offset `2`) is
"Smallest x + y*z, given x*y + z = n (for positive integers x, y, z)."

## Encoding

* The `n X k` rectangle is the closed box `[0, n] × [0, k]` in the plane.
* A lattice rectangle is given by one vertex `(x₀, y₀) ∈ ℤ²` and two perpendicular integer side
  vectors `u = (u₁, u₂)`, `v = (v₁, v₂)`; its vertices are `P₀ = (x₀, y₀)`, `P₀ + u`,
  `P₀ + u + v`, `P₀ + v`. Every rectangle with integer vertices arises this way (squares included).
* "No side parallel to the x-axis": every side is parallel to `u` or to `v`, so this is
  `u₂ ≠ 0 ∧ v₂ ≠ 0`; in particular `u, v ≠ 0`, so the rectangle is non-degenerate.
* "Touching all four sides of the n X k rectangle" is read as: the lattice rectangle lies inside
  the box (i.e. all four vertices do, the rectangle being their convex hull) and meets each of the
  four sides. For a convex polygon inside the box, meeting the side on the line `x = 0` (resp.
  `x = n`, `y = 0`, `y = k`) is the same as having a vertex on that line.
* `InRow n k` is this geometric condition. We prove (`inRow_iff_param`) that it is equivalent to
  `∃ a b c d > 0, a + b = n ∧ c + d = k ∧ a * b = c * d`, deduce the bound
  `k ≤ n * n / 4 + 1` for every `k` in row `n`, and so the finite list `row n` (computed by a
  bounded search, increasing) has exactly the members of row `n` (`mem_row`). The flattened
  sequence `a` uses the OEIS indexing of the b-file (`a 2, a 3, …` are the terms, row by row).
* `A228286 n` is the minimum of `x + y * z` over the (finitely many) positive triples with
  `x * y + z = n`, computed by a bounded search; `isLeast_A228286` certifies it for `n ≥ 2`.
* The conjecture concerns every row, i.e. every `n ≥ 2`.
-/

namespace Math0.Statements.A338885

/-- The integer point `(x, y)` lies in the closed box `[0, n] × [0, k]`. -/
def InBox (n k : ℕ) (p : ℤ × ℤ) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ n ∧ 0 ≤ p.2 ∧ p.2 ≤ k

/-- The four vertices `P₀, P₀ + u, P₀ + u + v, P₀ + v` of the lattice rectangle with corner
`P₀ = (x₀, y₀)` and side vectors `u = (u₁, u₂)`, `v = (v₁, v₂)`. -/
def vertices (x₀ y₀ u₁ u₂ v₁ v₂ : ℤ) : List (ℤ × ℤ) :=
  [(x₀, y₀), (x₀ + u₁, y₀ + u₂), (x₀ + u₁ + v₁, y₀ + u₂ + v₂), (x₀ + v₁, y₀ + v₂)]

/-- `k` belongs to the `n`-th row: there is a diagonal lattice rectangle (integer vertices,
perpendicular sides, no side parallel to the x-axis) lying in the `n X k` box `[0, n] × [0, k]`
and touching all four of its sides. -/
def InRow (n k : ℕ) : Prop :=
  ∃ x₀ y₀ u₁ u₂ v₁ v₂ : ℤ,
    -- the sides `u` and `v` are perpendicular (so the parallelogram is a rectangle)
    u₁ * v₁ + u₂ * v₂ = 0 ∧
    -- no side is parallel to the x-axis
    u₂ ≠ 0 ∧ v₂ ≠ 0 ∧
    -- the rectangle lies in the box
    (∀ p ∈ vertices x₀ y₀ u₁ u₂ v₁ v₂, InBox n k p) ∧
    -- it touches the sides `x = 0`, `x = n`, `y = 0`, `y = k`
    (∃ p ∈ vertices x₀ y₀ u₁ u₂ v₁ v₂, p.1 = 0) ∧
    (∃ p ∈ vertices x₀ y₀ u₁ u₂ v₁ v₂, p.1 = n) ∧
    (∃ p ∈ vertices x₀ y₀ u₁ u₂ v₁ v₂, p.2 = 0) ∧
    (∃ p ∈ vertices x₀ y₀ u₁ u₂ v₁ v₂, p.2 = k)

/-- Boolean search used to compute the rows: `a * (n - a) = c * (k - c)` for some
`0 < a < n`, `0 < c < k`. Justified by `inRowB_iff`. -/
def inRowB (n k : ℕ) : Bool :=
  (List.range' 1 (n - 1)).any fun a => (List.range' 1 (k - 1)).any fun c =>
    a * (n - a) == c * (k - c)

/-- The `n`-th row, in increasing order: all `k ≤ n * n / 4 + 1` with `inRowB n k`
(see `mem_row`: these are exactly the `k` with `InRow n k`). -/
def row (n : ℕ) : List ℕ :=
  (List.range (n * n / 4 + 2)).filter (inRowB n)

/-- Read the flattened triangle starting at row `n`, skipping `j` terms (`fuel` bounds the
number of rows visited; every row `n ≥ 2` is nonempty, so `fuel = i` suffices below). -/
def flatAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, n, j =>
    if j < (row n).length then (row n).getD j 0 else flatAux fuel (n + 1) (j - (row n).length)

/-- A338885 as a flattened sequence, indexed as in the OEIS b-file (`a 2` is the first term). -/
def a (i : ℕ) : ℕ := flatAux i 2 (i - 2)

/-! ### The rows: geometric definition versus the computed list -/

/-- The four side lengths of a diagonal rectangle in the box: `InRow n k` iff
`n = a + b`, `k = c + d` and `a * b = c * d` for some positive `a, b, c, d`. -/
theorem inRow_iff_param (n k : ℕ) :
    InRow n k ↔ ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a + b = n ∧ c + d = k ∧ a * b = c * d := by
  constructor
  · rintro ⟨x₀, y₀, u₁, u₂, v₁, v₂, hperp, hu, hv, hbox, h0, hn, h0', hk⟩
    simp only [vertices, InBox, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      forall_const, and_true] at hbox
    simp only [vertices, List.mem_cons, List.not_mem_nil, or_false, or_and_right, exists_or,
      exists_eq_left] at h0 hn h0' hk
    have huv : u₂ * v₂ ≠ 0 := mul_ne_zero hu hv
    have hu₁ : u₁ ≠ 0 := by rintro rfl; apply huv; linarith
    have hv₁ : v₁ ≠ 0 := by rintro rfl; apply huv; linarith
    have hprod : u₁.natAbs * v₁.natAbs = u₂.natAbs * v₂.natAbs := by
      have h := congrArg Int.natAbs (show u₁ * v₁ = -(u₂ * v₂) by linarith)
      simpa [Int.natAbs_mul, Int.natAbs_neg] using h
    refine ⟨u₁.natAbs, v₁.natAbs, u₂.natAbs, v₂.natAbs, Int.natAbs_pos.mpr hu₁,
      Int.natAbs_pos.mpr hv₁, Int.natAbs_pos.mpr hu, Int.natAbs_pos.mpr hv, ?_, ?_, hprod⟩
    · omega
    · omega
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, hn, hk, hab⟩
    subst hn hk
    refine ⟨b, 0, a, c, -b, d, ?_, by exact_mod_cast hc.ne', by exact_mod_cast hd.ne', ?_, ?_, ?_,
      ?_, ?_⟩
    · have : ((a * b : ℕ) : ℤ) = ((c * d : ℕ) : ℤ) := by rw [hab]
      push_cast at this; linarith
    all_goals simp [vertices, InBox]
    all_goals omega

theorem inRowB_iff (n k : ℕ) :
    inRowB n k = true ↔ ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a + b = n ∧ c + d = k ∧ a * b = c * d := by
  simp only [inRowB, List.any_eq_true, List.mem_range'_1, beq_iff_eq]
  constructor
  · rintro ⟨a, ⟨ha1, ha2⟩, c, ⟨hc1, hc2⟩, h⟩
    exact ⟨a, n - a, c, k - c, by omega, by omega, by omega, by omega, by omega, by omega, h⟩
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, rfl, rfl, h⟩
    exact ⟨a, ⟨ha, by omega⟩, c, ⟨hc, by omega⟩, by simpa using h⟩

/-- Every member of row `n` is at most `n * n / 4 + 1`. -/
theorem le_of_inRow {n k : ℕ} (h : InRow n k) : k ≤ n * n / 4 + 1 := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl, rfl, hab⟩ := (inRow_iff_param _ _).1 h
  have h1 : c + d ≤ c * d + 1 := by nlinarith
  have h2 : a * b ≤ (a + b) * (a + b) / 4 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    zify
    nlinarith [sq_nonneg ((a : ℤ) - b)]
  omega

/-- `row n` lists exactly the members of the `n`-th row. -/
theorem mem_row (n k : ℕ) : k ∈ row n ↔ InRow n k := by
  rw [row, List.mem_filter, List.mem_range, inRowB_iff, ← inRow_iff_param]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by have := le_of_inRow h; omega, h⟩

/-- `row n` is strictly increasing, as the OEIS rows are listed. -/
theorem row_sorted (n : ℕ) : (row n).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

/-- The first terms listed in OEIS (rows 2 to 12 complete and the start of row 13),
kernel-checked. -/
theorem a_data : (List.range 71).map (fun i => a (i + 2)) =
    [2, 3, 4, 5, 4, 5, 7, 6, 9, 10, 5, 7, 8, 11, 13, 7, 8, 10, 13, 16, 17, 6, 9, 11, 12, 15, 19,
      21, 6, 8, 10, 11, 14, 17, 22, 25, 26, 7, 9, 10, 11, 13, 14, 16, 17, 19, 25, 29, 31, 9, 12,
      13, 15, 18, 20, 21, 28, 33, 36, 37, 7, 8, 11, 12, 13, 14, 15, 17, 20, 22, 23] := by
  decide +kernel

/-! ### A228286 -/

/-- The values `x + y * z` over positive integers `x, y, z` with `x * y + z = n`. -/
def A228286Set (n : ℕ) : Set ℕ :=
  {m | ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x * y + z = n ∧ m = x + y * z}

/-- The list of the values `x + y * (n - x * y)` over `0 < x, y < n` with `x * y < n`. -/
def A228286List (n : ℕ) : List ℕ :=
  (List.range' 1 (n - 1)).flatMap fun x => (List.range' 1 (n - 1)).filterMap fun y =>
    if x * y < n then some (x + y * (n - x * y)) else none

/-- A228286: smallest `x + y * z`, given `x * y + z = n` (for positive integers `x, y, z`);
computed as the minimum of `A228286List n` (see `isLeast_A228286`). -/
def A228286 (n : ℕ) : ℕ := (A228286List n).min?.getD 0

theorem mem_A228286List (n m : ℕ) : m ∈ A228286List n ↔ m ∈ A228286Set n := by
  simp only [A228286List, List.mem_flatMap, List.mem_range'_1, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, A228286Set, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, y, ⟨hy1, hy2⟩, hxy, rfl⟩
    exact ⟨x, y, n - x * y, by omega, by omega, by omega, by omega, rfl⟩
  · rintro ⟨x, y, z, hx, hy, hz, rfl, rfl⟩
    have h1 : x ≤ x * y := Nat.le_mul_of_pos_right x hy
    have h2 : y ≤ x * y := Nat.le_mul_of_pos_left y hx
    exact ⟨x, ⟨hx, by omega⟩, y, ⟨hy, by omega⟩, by omega, by
      rw [show x * y + z - x * y = z by omega]⟩

/-- `A228286 n` is the least element of `A228286Set n` for `n ≥ 2` (the OEIS range). -/
theorem isLeast_A228286 {n : ℕ} (hn : 2 ≤ n) : IsLeast (A228286Set n) (A228286 n) := by
  have hne : A228286List n ≠ [] := by
    intro h
    have : n - 1 + 1 * 1 ∈ A228286List n := by
      rw [mem_A228286List]
      exact ⟨n - 1, 1, 1, by omega, by omega, by omega, by omega, rfl⟩
    rw [h] at this
    simp at this
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (List.isSome_min?_of_ne_nil hne)
  rw [A228286, hm, Option.getD_some]
  obtain ⟨hmem, hle⟩ := List.min?_eq_some_iff.mp hm
  exact ⟨(mem_A228286List n m).1 hmem, fun b hb => hle b ((mem_A228286List n b).2 hb)⟩

/-- A228286 (offset 2) reproduces its first 70 listed OEIS terms (kernel-checked). -/
theorem A228286_data : (List.range 70).map (fun i => A228286 (i + 2)) =
    [2, 3, 4, 4, 6, 5, 7, 6, 6, 7, 9, 7, 10, 9, 8, 8, 12, 9, 12, 9, 10, 13, 15, 10, 10, 15, 12,
      11, 15, 11, 16, 12, 14, 17, 12, 12, 17, 21, 16, 13, 18, 13, 19, 15, 14, 19, 24, 14, 14, 15,
      20, 17, 21, 15, 16, 15, 22, 25, 28, 16, 22, 27, 16, 16, 18, 17, 23, 21, 25, 17] := by
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Kagey, A338885): for every row `n ≥ 2`, the smallest number `k` such that a
diagonal lattice rectangle touches all four sides of the `n X k` box is `A228286 n`. -/
def statement : Prop :=
  ∀ n : ℕ, 2 ≤ n → IsLeast {k : ℕ | InRow n k} (A228286 n)

end Math0.Statements.A338885
