/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A057566: Layman's floor formula for collinear triples in a `3 × n` grid

Source: https://oeis.org/A057566, John W. Layman (author of the entry), Oct 04 2000 (FORMULA
section). Verbatim:
> Conjecture: a(n) = 5*floor((2n^3 - 3n^2 - n)/24) + floor((2(n-1)^3 - 3(n-1)^2 - (n-1))/24) + n,
> which fits all of the listed terms.

The sequence (offset `0`) is "Number of collinear triples in a 3 X n rectangular grid."

## Encoding

* The `3 × n` grid is `grid n = {0, 1, 2} × {0, …, n - 1} ⊆ ℕ × ℕ` (row, column); it has `3n`
  points (for `n = 0` it is empty).
* Three lattice points `p, q, r` are collinear iff the determinant
  `cross p q r = (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)` (twice the signed area of
  the triangle `p q r`, computed in `ℤ`) vanishes. A finite set of points is collinear
  (`IsCollinear`) iff every three of its points (with repetitions allowed) satisfy this.
  `isCollinear_triple` shows that for a set `{p, q, r}` this is just `cross p q r = 0`.
* A "collinear triple" is a 3-element subset of the grid that is collinear, so
  `a n = #{s ⊆ grid n | #s = 3 ∧ IsCollinear s}`, written with `Finset.powersetCard 3`.
* `a` is computable but too slow for the kernel, so `fastA` counts the same triples by a nested
  list recursion over the increasing index triples of the list `pts n` of grid points, with the
  collinearity test rearranged into an equation of natural numbers. `a_eq_fastA` proves
  `a n = fastA n` for every `n`, and `a_data` checks the listed terms `a 0, …, a 24` (this
  includes `a 24 = 6360`).
* The floors are `Int.floor` of rational numbers, and `n - 1` is the rational (equivalently
  integer) `n - 1`, so for `n = 0` it is `-1` (not truncated to `0`).
* Range of `n`: the conjecture gives none, and the sequence has offset `0`. However, for
  `n = 0, 1, 2` some floor arguments are negative (`(2m^3 - 3m^2 - m)/24` is `-4/24` at
  `m = -1` and `-2/24` at `m = 1`), and there the value of the formula depends on the rounding
  convention: with the true floor (`⌊-1/6⌋ = -1`) it gives `-1, -4, 1` instead of `0, 1, 2`,
  while with rounding toward zero (which sends those small negative quotients to `0`) it gives
  exactly `0, 1, 2` and then agrees with every term `a 0, …, a 23`. That is consistent with the
  author's remark "which fits all of the listed terms" if the listing then ran up to `a 23`.
  To keep the formalization from being refuted by this rounding artefact at the degenerate
  sizes `n ≤ 2` (an empty grid or one with fewer than three columns), the primary
  formalization `statement` asserts the identity for every `n ≥ 3`. For those `n`, both floor
  arguments are `≥ 0`, so floor and truncation coincide and every reading of "floor" gives
  the same claim. The literal reading for every `n ≥ 0` with true floors is recorded as the
  stronger variant `statement_all`, together with `statement_all_imp : statement_all → statement`.
  The remark "which fits all of the listed terms" is the author's evidence, not part of the
  claimed identity.
* `statement_iff_ediv` restates `statement` with integer division `/` (which is floor division
  for the positive divisor `24`) in place of the rational floors.
-/

namespace Math0.Statements.A057566

/-- The `3 × n` rectangular grid: lattice points `(i, j)` with row `i < 3` and column `j < n`. -/
def grid (n : ℕ) : Finset (ℕ × ℕ) := Finset.range 3 ×ˢ Finset.range n

/-- The determinant `(q - p) × (r - p)`, i.e. twice the signed area of the triangle `p q r`;
it vanishes iff `p`, `q`, `r` lie on a common line. -/
def cross (p q r : ℕ × ℕ) : ℤ :=
  ((q.1 : ℤ) - p.1) * ((r.2 : ℤ) - p.2) - ((q.2 : ℤ) - p.2) * ((r.1 : ℤ) - p.1)

/-- A finite set of lattice points is collinear iff any three of its points are collinear. -/
def IsCollinear (s : Finset (ℕ × ℕ)) : Prop := ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, cross p q r = 0

instance : DecidablePred IsCollinear := fun s => by unfold IsCollinear; infer_instance

/-- A057566: the number of collinear triples (3-element collinear subsets) in the `3 × n`
rectangular grid. -/
def a (n : ℕ) : ℕ := ((grid n).powersetCard 3 |>.filter IsCollinear).card

/-! ### A fast evaluator for the data check -/

/-- The collinearity test `cross p q r = 0`, rearranged into an equation of natural numbers. -/
def collB (p q r : ℕ × ℕ) : Bool :=
  Nat.beq (q.1 * r.2 + q.2 * p.1 + p.2 * r.1) (q.2 * r.1 + q.1 * p.2 + p.1 * r.2)

/-- Number of `r` in `l` with `p, q, r` collinear. -/
def cnt2 (p q : ℕ × ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | r :: l => cnt2 p q l + (if collB p q r then 1 else 0)

/-- Number of pairs `q, r` (in this order) in `l` with `p, q, r` collinear. -/
def cnt1 (p : ℕ × ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | q :: l => cnt1 p l + cnt2 p q l

/-- Number of collinear triples `p, q, r` (in this order) in `l`. -/
def cnt : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: l => cnt l + cnt1 p l

/-- The points of `grid n`, listed once each. -/
def pts (n : ℕ) : List (ℕ × ℕ) := List.range 3 ×ˢ List.range n

/-- Fast evaluator of `a`. -/
def fastA (n : ℕ) : ℕ := cnt (pts n)

/-- Collinearity of a multiset of points. -/
def Q (m : Multiset (ℕ × ℕ)) : Prop := ∀ p ∈ m, ∀ q ∈ m, ∀ r ∈ m, cross p q r = 0

instance : DecidablePred Q := fun s => by unfold Q; infer_instance

theorem collB_iff (p q r : ℕ × ℕ) : collB p q r = true ↔ cross p q r = 0 := by
  unfold collB cross
  rw [Nat.beq_eq]
  constructor
  · intro h
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    push_cast at h'
    linear_combination h'
  · intro h
    have h' : ((q.1 * r.2 + q.2 * p.1 + p.2 * r.1 : ℕ) : ℤ) =
        ((q.2 * r.1 + q.1 * p.2 + p.1 * r.2 : ℕ) : ℤ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'

theorem Q_triple (p q r : ℕ × ℕ) : Q (([p, q, r] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) ↔
    cross p q r = 0 := by
  unfold Q
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h
    exact h p (Or.inl rfl) q (Or.inr (Or.inl rfl)) r (Or.inr (Or.inr rfl))
  · intro h x hx y hy z hz
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl <;> unfold cross at * <;>
      first | ring1 | linear_combination h | linear_combination -h

/-- For a set of three points, `IsCollinear` is the vanishing of `cross`. -/
theorem isCollinear_triple (p q r : ℕ × ℕ) :
    IsCollinear {p, q, r} ↔ cross p q r = 0 := by
  unfold IsCollinear
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    exact h p (Or.inl rfl) q (Or.inr (Or.inl rfl)) r (Or.inr (Or.inr rfl))
  · intro h x hx y hy z hz
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl <;> unfold cross at * <;>
      first | ring1 | linear_combination h | linear_combination -h

theorem countP_one (p q : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    (l.sublistsLen 1).countP (fun t => decide (Q ((p :: q :: t : List (ℕ × ℕ)) :
      Multiset (ℕ × ℕ)))) = cnt2 p q l := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rw [List.sublistsLen_succ_cons, List.countP_append, ih]
    simp only [List.sublistsLen_zero, List.map_cons, List.map_nil, cnt2]
    congr 1
    rw [List.countP_singleton]
    by_cases h : collB p q r = true
    · simp [h, Q_triple, (collB_iff p q r).1 h]
    · have h' : ¬ cross p q r = 0 := fun h'' => h ((collB_iff p q r).2 h'')
      simp [h, Q_triple, h']

theorem countP_two (p : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    (l.sublistsLen 2).countP (fun t => decide (Q ((p :: t : List (ℕ × ℕ)) :
      Multiset (ℕ × ℕ)))) = cnt1 p l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [List.sublistsLen_succ_cons, List.countP_append, ih, List.countP_map]
    simp only [cnt1]
    congr 1
    rw [← countP_one p q l]
    rfl

theorem countP_three (l : List (ℕ × ℕ)) :
    (l.sublistsLen 3).countP (fun t : List (ℕ × ℕ) => decide (Q (↑t : Multiset (ℕ × ℕ)))) =
      cnt l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.sublistsLen_succ_cons, List.countP_append, ih, List.countP_map]
    simp only [cnt]
    congr 1
    rw [← countP_two p l]
    rfl

theorem grid_val (n : ℕ) : (grid n).val = ((pts n : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  rfl

/-- The fast evaluator computes `a`. -/
theorem a_eq_fastA (n : ℕ) : a n = fastA n := by
  unfold a fastA
  rw [Finset.card_def, Finset.filter_val, ← Multiset.countP_eq_card_filter]
  have h1 : Multiset.countP IsCollinear ((grid n).powersetCard 3).val =
      Multiset.countP Q (((grid n).powersetCard 3).val.map Finset.val) := by
    rw [Multiset.countP_map, Multiset.countP_eq_card_filter]
    rfl
  rw [h1, Finset.map_val_val_powersetCard, grid_val, Multiset.powersetCard_coe,
    Multiset.coe_countP, List.countP_map, ← countP_three]
  rfl

/-- The definition reproduces the first terms listed in OEIS (kernel-checked):
`a 0, …, a 24`. -/
theorem a_data : (List.range 25).map (fun i => a (i + 0)) =
    [0, 1, 2, 8, 20, 43, 78, 130, 200, 293, 410, 556, 732, 943, 1190, 1478, 1808, 2185,
      2610, 3088, 3620, 4211, 4862, 5578, 6360] := by
  simp only [Nat.add_zero, a_eq_fastA]
  decide +kernel

/-- Layman's conjecture, for every `n ≥ 3` (where all floor arguments are nonnegative, so the
claim does not depend on the rounding convention; see the module docstring):
`a(n) = 5*floor((2n^3 - 3n^2 - n)/24) + floor((2(n-1)^3 - 3(n-1)^2 - (n-1))/24) + n`. -/
def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → (a n : ℤ) =
    5 * ⌊(2 * (n : ℚ) ^ 3 - 3 * (n : ℚ) ^ 2 - (n : ℚ)) / 24⌋
      + ⌊(2 * ((n : ℚ) - 1) ^ 3 - 3 * ((n : ℚ) - 1) ^ 2 - ((n : ℚ) - 1)) / 24⌋ + n

/-- The literal reading of Layman's conjecture for every `n ≥ 0`, with true floors (not the
primary formalization; at `n = 0, 1, 2` it hinges on the floor of a small negative number, see
the module docstring). -/
def statement_all : Prop :=
  ∀ n : ℕ, (a n : ℤ) =
    5 * ⌊(2 * (n : ℚ) ^ 3 - 3 * (n : ℚ) ^ 2 - (n : ℚ)) / 24⌋
      + ⌊(2 * ((n : ℚ) - 1) ^ 3 - 3 * ((n : ℚ) - 1) ^ 2 - ((n : ℚ) - 1)) / 24⌋ + n

theorem statement_all_imp : statement_all → statement :=
  fun h n _ => h n

/-- `statement` with the rational floors written as integer floor division. -/
theorem statement_iff_ediv : statement ↔ ∀ n : ℕ, 3 ≤ n → (a n : ℤ) =
    5 * ((2 * (n : ℤ) ^ 3 - 3 * (n : ℤ) ^ 2 - (n : ℤ)) / 24)
      + ((2 * ((n : ℤ) - 1) ^ 3 - 3 * ((n : ℤ) - 1) ^ 2 - ((n : ℤ) - 1)) / 24) + n := by
  have key : ∀ m : ℤ, ⌊(2 * (m : ℚ) ^ 3 - 3 * (m : ℚ) ^ 2 - (m : ℚ)) / 24⌋ =
      (2 * m ^ 3 - 3 * m ^ 2 - m) / 24 := by
    intro m
    have := Rat.floor_intCast_div_natCast (2 * m ^ 3 - 3 * m ^ 2 - m) 24
    push_cast at this
    exact this
  unfold statement
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  have h1 := key (n : ℤ)
  have h2 := key ((n : ℤ) - 1)
  push_cast at h1 h2
  rw [h1, h2]

end Math0.Statements.A057566
