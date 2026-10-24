/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A223395: walks on the 4 × 4 grid graph (n × 1 arrays)

Source: https://oeis.org/A223395, _R. H. Hardin_, Mar 19 2013 (Barker's conjectures added
Aug 20 2018). Verbatim (FORMULA section):
> Empirical: a(n) = 3*a(n-1) + 2*a(n-2) - 4*a(n-3).
> Conjectures from _Colin Barker_, Aug 20 2018: (Start)
> G.f.: 8*x*(2 - 3*x^2) / ((1 - x)*(1 - 2*x - 4*x^2)).
> a(n) = (8 + (11-5*sqrt(5))*(1-sqrt(5))^n + (1+sqrt(5))^n*(11+5*sqrt(5))) / 5.
> (End)

The entry's name: "4 X 4 square grid graph coloring a rectangular array: number of n X 1 0..15
arrays where 0..15 label nodes of the square grid graph and every array movement to a horizontal
or vertical neighbor moves along an edge of this graph." Offset `1`.

## Encoding

* The nodes `0..15` are `Fin 16`; node `k` sits in row `k / 4` and column `k % 4` of the 4 × 4
  grid, and two nodes are adjacent (`Adj`) iff they are horizontal or vertical neighbours in the
  grid. `adj_iff_entry` checks (in the kernel) that this is exactly the neighbour list printed in
  the entry's EXAMPLE section ("0 -> 1 4", "1 -> 0 2 5", ..., "15 -> 14 11").
* An `n X 1` array is a single column of `n` entries, encoded as `f : Fin n → Fin 16` (entry in
  row `i` is `f i`). It has no horizontal neighbours, and its vertical neighbours are the entries
  in rows `i` and `i + 1`; since the grid graph is undirected (`Adj` is symmetric, so moving down
  or up gives the same condition) and loopless, the condition is `Valid f`: `Adj (f i) (f (i+1))`
  for all consecutive rows. `a n` is the number of valid
  columns (`Fintype.card`), i.e. the number of walks with `n` vertices in the grid graph.
  The OEIS offset is `1`; `a 0 = 1` (the empty array) is not a term of the sequence.
* The kernel cannot enumerate `16^n` columns, so the data check goes through the transfer-matrix
  version `aL` (a list-based dynamic programme on `cnt n v`, the number of valid columns with
  `n + 1` entries and top entry `v`), proved equal to `a` for every `n` (`a_eq_aL`); `a_data`
  then checks all 24 listed terms `a(1..24)` with `decide +kernel`.
* Hardin's recurrence has no stated range; with offset `1` it is read for every `n ≥ 4` (the
  first `n` for which `a(n-3)` is a term). It is stated in `ℤ` because of the subtraction
  (`statementRec`).
* Barker's g.f. is the formal power series `∑_{n ≥ 1} a(n) x^n` over `ℤ`; it is stated after
  clearing the denominator `(1 - x)(1 - 2x - 4x^2)`, which has constant term `1` and is therefore
  a unit in `ℤ⟦X⟧`, so this is equivalent (`statementGF`).
* Barker's closed form is stated in `ℝ` for every term, i.e. every `n ≥ 1` (`statementClosedForm`).
* `statement` is the conjunction of the three conjectures recorded in the entry.
-/

namespace Math0.Statements.A223395

/-- Adjacency in the 4 × 4 square grid graph on nodes `0..15`, node `k` being in row `k / 4` and
column `k % 4`: two nodes are adjacent iff they are horizontal or vertical neighbours. -/
def Adj (i j : Fin 16) : Prop :=
  (i.val / 4 = j.val / 4 ∧ (i.val % 4 + 1 = j.val % 4 ∨ j.val % 4 + 1 = i.val % 4)) ∨
    (i.val % 4 = j.val % 4 ∧ (i.val / 4 + 1 = j.val / 4 ∨ j.val / 4 + 1 = i.val / 4))

instance : DecidableRel Adj := fun i j => by unfold Adj; infer_instance

/-- The "Vertex neighbors" list printed in the entry. -/
def entryNbrs : Fin 16 → List (Fin 16) :=
  ![[1, 4], [0, 2, 5], [1, 3, 6], [2, 7], [0, 5, 8], [4, 1, 6, 9], [5, 2, 7, 10], [6, 3, 11],
    [4, 9, 12], [8, 5, 10, 13], [9, 6, 11, 14], [10, 7, 15], [8, 13], [12, 9, 14],
    [13, 10, 15], [14, 11]]

/-- `Adj` is exactly the neighbour relation listed in the entry (kernel-checked). -/
theorem adj_iff_entry : ∀ i j : Fin 16, Adj i j ↔ j ∈ entryNbrs i := by decide +kernel

/-- An `n X 1` array (a column `f`, entry in row `i` being `f i`) is valid iff every two
vertically neighbouring entries are adjacent nodes of the grid graph. -/
def Valid {n : ℕ} (f : Fin n → Fin 16) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → Adj (f i) (f j)

instance (n : ℕ) : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

/-- A223395: the number of `n X 1` arrays with entries in `0..15` (nodes of the 4 × 4 square grid
graph) such that every move to a vertical neighbour moves along an edge of the graph. -/
def a (n : ℕ) : ℕ := Fintype.card {f : Fin n → Fin 16 // Valid f}

/-! ### A fast, provably equal version for the data check -/

/-- Number of valid columns with `n + 1` entries whose top entry is `v`. -/
def cnt (n : ℕ) (v : Fin 16) : ℕ :=
  ∑ f : Fin (n + 1) → Fin 16, if Valid f ∧ f 0 = v then 1 else 0

/-- One transfer-matrix step on a vector stored as a list of length 16. -/
def stepL (l : List ℕ) : List ℕ :=
  (List.finRange 16).map fun v =>
    ((List.finRange 16).map fun u => if Adj v u then l.getD u.val 0 else 0).sum

/-- `colsL n` lists `cnt n v` for `v = 0, …, 15`. -/
def colsL : ℕ → List ℕ
  | 0 => List.replicate 16 1
  | n + 1 => stepL (colsL n)

/-- Fast computation of `a`. -/
def aL : ℕ → ℕ
  | 0 => 1
  | n + 1 => (colsL n).sum

theorem valid_cons {n : ℕ} (x : Fin 16) (g : Fin (n + 1) → Fin 16) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 16) ↔ Adj x (g 0) ∧ Valid g := by
  constructor
  · intro h
    refine ⟨?_, fun i j hij => ?_⟩
    · simpa using h 0 1 (by simp)
    · simpa using h i.succ j.succ (by simp [hij])
  · rintro ⟨h0, hg⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have hj : j = 0 := by ext; simp at hij; omega
        subst hj
        simpa using h0
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j => simpa using hg i j (by simpa using hij)

theorem cnt_zero (v : Fin 16) : cnt 0 v = 1 := by
  unfold cnt
  rw [← (Equiv.funUnique (Fin 1) (Fin 16)).symm.sum_comp]
  have hv : ∀ x : Fin 16, Valid ((Equiv.funUnique (Fin 1) (Fin 16)).symm x) := by
    intro x i j hij
    have hi := i.isLt
    have hj := j.isLt
    omega
  rw [Finset.sum_eq_single v]
  · rw [if_pos ⟨hv v, rfl⟩]
  · intro b _ hb
    rw [if_neg]
    rintro ⟨_, h⟩
    exact hb h
  · intro h
    exact absurd (Finset.mem_univ v) h

/-- Splitting off the top entry of a column. -/
theorem sum_cons (n : ℕ) (F : (Fin (n + 1) → Fin 16) → ℕ) :
    ∑ f, F f = ∑ x, ∑ g : Fin n → Fin 16, F (Fin.cons x g) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 16).symm _ _ (fun f => by simp)

theorem cnt_succ (n : ℕ) (v : Fin 16) :
    cnt (n + 1) v = ∑ u, if Adj v u then cnt n u else 0 := by
  unfold cnt
  rw [sum_cons]
  simp only [valid_cons, Fin.cons_zero]
  calc
    _ = ∑ g : Fin (n + 1) → Fin 16, if Adj v (g 0) ∧ Valid g then 1 else 0 := by
      rw [Finset.sum_eq_single v]
      · simp
      · intro b _ hb
        apply Finset.sum_eq_zero
        intro g _
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ v) h
    _ = ∑ g : Fin (n + 1) → Fin 16, ∑ u,
          if Adj v u then (if Valid g ∧ g 0 = u then 1 else 0) else 0 := by
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.sum_eq_single (g 0)]
      · by_cases h1 : Adj v (g 0) <;> by_cases h2 : Valid g <;> simp [h1, h2]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h : Adj v u <;> simp [h]

theorem a_zero : a 0 = 1 := by
  unfold a
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨finZeroElim, fun i => i.elim0⟩, fun f => ?_⟩
  ext i
  exact i.elim0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ v, cnt n v := by
  unfold a cnt
  rw [Fintype.card_subtype, Finset.card_filter, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_eq_single (f 0)]
  · by_cases h : Valid f <;> simp [h]
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem getD_map_finRange (w : Fin 16 → ℕ) (u : Fin 16) :
    ((List.finRange 16).map w).getD u.val 0 = w u := by
  simp [List.getD_eq_getElem?_getD]

theorem colsL_eq (n : ℕ) : colsL n = (List.finRange 16).map (cnt n) := by
  induction n with
  | zero =>
    rw [show cnt 0 = fun _ => 1 from funext cnt_zero]
    rfl
  | succ n ih =>
    simp only [colsL, stepL, ih, getD_map_finRange]
    refine List.map_congr_left fun v _ => ?_
    rw [cnt_succ, Fin.sum_univ_def]

/-- `a` agrees with the fast transfer-matrix version `aL` for every `n`. -/
theorem a_eq_aL (n : ℕ) : a n = aL n := by
  cases n with
  | zero => simp [a_zero, aL]
  | succ n => rw [a_succ, aL, colsL_eq, Fin.sum_univ_def]

/-- The definition reproduces the first 24 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 24).map (fun i => a (i + 1)) =
    [16, 48, 152, 488, 1576, 5096, 16488, 53352, 172648, 558696, 1807976, 5850728,
      18933352, 61269608, 198272616, 641623656, 2076337768, 6719170152,
      21743691368, 70364063336, 227702892136, 736862037608, 2384535643752,
      7716519437928] := by
  simp only [a_eq_aL]
  decide +kernel

/-- Hardin's empirical recurrence: `a(n) = 3 a(n-1) + 2 a(n-2) - 4 a(n-3)` for every `n ≥ 4`. -/
def statementRec : Prop :=
  ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) + 2 * a (n - 2) - 4 * a (n - 3)

/-- Barker's conjectured generating function:
`∑_{n ≥ 1} a(n) x^n = 8 x (2 - 3 x^2) / ((1 - x)(1 - 2x - 4x^2))`, with the (unit)
denominator cleared. -/
def statementGF : Prop :=
  (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) =
    8 * PowerSeries.X * (2 - 3 * PowerSeries.X ^ 2)

/-- Barker's conjectured closed form, for every term `n ≥ 1`:
`a(n) = (8 + (11 - 5√5)(1 - √5)^n + (1 + √5)^n (11 + 5√5)) / 5`. -/
def statementClosedForm : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    (8 + (11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ n +
      (1 + Real.sqrt 5) ^ n * (11 + 5 * Real.sqrt 5)) / 5

/-- The conjectures of A223395: Hardin's recurrence `a(n) = 3a(n-1) + 2a(n-2) - 4a(n-3)`
(`n ≥ 4`), together with Barker's generating function and closed form. -/
def statement : Prop := statementRec ∧ statementGF ∧ statementClosedForm

end Math0.Statements.A223395
